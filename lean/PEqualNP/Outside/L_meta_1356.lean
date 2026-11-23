import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1356_aux

open PEqualNP.CircuitLowerBounds

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem prefixValue (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (gs.foldl step (step w g)).getD i false = _
    rw [ih (step w g) (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ hi

private theorem firstValue {n : ℕ} (g : Gate) (gs : List Gate) (x : Fin n → Bool) :
    Circuit.eval ⟨g :: gs, n⟩ (List.ofFn x) =
      g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false) := by
  change (gs.foldl step (step (List.ofFn x) g)).getD n false = _
  rw [prefixValue _ _ _ (by simp [step])]
  unfold step
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp

private theorem inputValue {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (p : Fin n) :
    Circuit.eval ⟨gs, p.val⟩ (List.ofFn x) = x p := by
  change (gs.foldl step (List.ofFn x)).getD p.val false = _
  rw [prefixValue _ _ _ (by simp)]
  simp

-- Compare wire values away from the raw input positions changed by a test.
private def Off (skip : ℕ → Prop) (r : Bool → Bool → Prop)
    (w w' : List Bool) : Prop :=
  w.length = w'.length ∧ ∀ i, ¬ skip i → r (w.getD i false) (w'.getD i false)

private theorem offSnoc {skip r w w' a b} (h : Off skip r w w') (hab : r a b) :
    Off skip r (w ++ [a]) (w' ++ [b]) := by
  refine ⟨by simp [h.1], fun i hi => ?_⟩
  by_cases il : i < w.length
  · rw [List.getD_append _ _ _ _ il, List.getD_append _ _ _ _ (by rw [← h.1]; exact il)]
    exact h.2 i hi
  · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by rw [← h.1]; omega), ← h.1]
    cases d : i - w.length with
    | zero => simpa using hab
    | succ j =>
      have h0 := h.2 i hi
      rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by rw [← h.1]; omega)] at h0
      simpa using h0

private theorem offFold {skip r} (gs : List Gate)
    (preserve : ∀ g ∈ gs, ∀ w w', Off skip r w w' →
      r (g.op.eval (g.inputs.map fun i => w.getD i false))
         (g.op.eval (g.inputs.map fun i => w'.getD i false))) :
    ∀ w w', Off skip r w w' → Off skip r (gs.foldl step w) (gs.foldl step w') := by
  induction gs with
  | nil => exact fun _ _ h => h
  | cons g gs ih =>
    intro w w' h
    change Off skip r (gs.foldl step (step w g)) (gs.foldl step (step w' g))
    exact ih (fun g' hm => preserve g' (List.mem_cons_of_mem _ hm)) _ _
      (offSnoc h (preserve g List.mem_cons_self w w' h))

private theorem offInput {n : ℕ} {skip r} {x y : Fin n → Bool}
    (h : ∀ i : Fin n, ¬ skip i.val → r (x i) (y i)) (r00 : r false false) :
    Off skip r (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp, fun j hj => ?_⟩
  by_cases jl : j < n
  · simpa [jl] using h ⟨j, jl⟩ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    exact r00

private def Binary (g : Gate) : Prop := g.op = GateOp.and ∨ g.op = GateOp.or

private def BinaryReads (g : Gate) (i : ℕ) : Prop := Binary g ∧ i ∈ g.inputs

private def NegReads (g : Gate) (i : ℕ) : Prop :=
  g.op = GateOp.not ∧ g.inputs.head? = some i

private theorem binaryMono {skip w w'} (g : Gate) (hg : Binary g)
    (safe : ∀ j ∈ g.inputs, ¬ skip j) (h : Off skip (fun a b => a = true → b = true) w w') :
    g.op.eval (g.inputs.map fun i => w.getD i false) = true →
    g.op.eval (g.inputs.map fun i => w'.getD i false) = true := by
  rcases hg with hg | hg
  · rw [hg]
    simp only [GateOp.eval, List.all_eq_true, List.mem_map, id]
    intro hl b hb
    obtain ⟨j, hj, rfl⟩ := hb
    exact h.2 j (safe j hj) (hl _ ⟨j, hj, rfl⟩)
  · rw [hg]
    simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
    rintro ⟨b, ⟨j, hj, rfl⟩, hb⟩
    exact ⟨_, ⟨j, hj, rfl⟩, h.2 j (safe j hj) hb⟩

private theorem inputBits {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    (List.ofFn x).getD i false = if h : i < n then x ⟨i, h⟩ else false := by
  by_cases hi : i < n
  · simp [hi]
  · rw [dite_eq_right hi, List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt hi)]

private theorem uniqueNeg {gs : List Gate} (pick : Fin 1 → Fin gs.length)
    (hpick : ∀ i : Fin gs.length, (gs.get i).op = GateOp.not → ∃ r : Fin 1, pick r = i)
    {i j : Fin gs.length} (hi : (gs.get i).op = GateOp.not) (hj : (gs.get j).op = GateOp.not) :
    i = j := by
  obtain ⟨a, ha⟩ := hpick i hi
  obtain ⟨b, hb⟩ := hpick j hj
  rw [← ha, ← hb, Subsingleton.elim a b]

private theorem pairSeparated {n m : ℕ} (S : Fin m → Finset (Fin n))
    (hmeet : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hcover : ∀ u : Fin n, ∃ i j : Fin m, i ≠ j ∧ u ∈ S i ∧ u ∈ S j)
    (p q : Fin n) (pq : p ≠ q) : ∃ i, p ∈ S i ∧ q ∉ S i := by
  obtain ⟨i, j, hij, hip, hjp⟩ := hcover p
  by_cases hiq : q ∈ S i
  · by_cases hjq : q ∈ S j
    · have hs : ({p,q} : Finset (Fin n)) ⊆ S i ∩ S j := by
        intro u hu
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with rfl | rfl <;> simp [hip, hjp, hiq, hjq]
      have hh := (Finset.card_le_card hs).trans (hmeet i j hij)
      rw [Finset.card_pair pq] at hh
      omega
    · exact ⟨j, hjp, hjq⟩
  · exact ⟨i, hip, hiq⟩

private theorem outputNotInput {n m : ℕ} (S : Fin m → Finset (Fin n))
    (hcard : ∀ o : Fin m, 2 ≤ (S o).card) (gs : List Gate) (out : Fin m → ℕ)
    (correct : ∀ (o : Fin m) (x : Fin n → Bool),
      Circuit.eval ⟨gs, out o⟩ (List.ofFn x) = decide (∃ v ∈ S o, x v = true)) :
    ∀ o : Fin m, n ≤ out o := by
  intro o
  by_contra! h
  let p : Fin n := ⟨out o,h⟩
  have hex : ∃ q ∈ S o, q ≠ p := by
    by_contra! hall
    have le : S o ⊆ {p} := by intro q hq; simpa using hall q hq
    have := Finset.card_le_card le
    simp at this
    have := hcard o
    omega
  obtain ⟨q, hq, qp⟩ := hex
  let x : Fin n → Bool := fun i => decide (i = q)
  have l : Circuit.eval ⟨gs,out o⟩ (List.ofFn x) = false := by
    change Circuit.eval ⟨gs,p.val⟩ (List.ofFn x) = false
    rw [inputValue]
    simp [x, qp.symm]
  rw [correct] at l
  exact (of_decide_eq_false l) ⟨q, hq, by simp [x]⟩

private theorem tailIndex (g : Gate) (gs : List Gate) {k : Gate} (hk : k ∈ gs) :
    ∃ i : Fin (g :: gs).length, i.val ≠ 0 ∧ (g :: gs).get i = k := by
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hk
  obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp hj
  exact ⟨⟨j+1, by simpa using Nat.succ_lt_succ hlt⟩, by simp, heq⟩


private def UniqueNot (gs : List Gate) : Prop :=
  ∀ i j : Fin gs.length, (gs.get i).op = GateOp.not →
    (gs.get j).op = GateOp.not → i = j

private theorem uniqueNotTail {g : Gate} {gs : List Gate}
    (hu : UniqueNot (g :: gs)) : UniqueNot gs := by
  intro i j hi hj
  have he := hu i.succ j.succ (by simpa using hi) (by simpa using hj)
  apply Fin.ext
  have hv := congrArg Fin.val he
  simp only [Fin.val_succ] at hv
  omega

private theorem offEqImp {p : ℕ} {w w' : List Bool}
    (he : Off (fun j => j = p) Eq w w') :
    Off (fun j => j = p) (fun a b => a = true → b = true) w w' := by
  refine ⟨he.1, ?_⟩
  intro j hj ht
  rw [← he.2 j hj]
  exact ht

private theorem oneNotFold (p : ℕ) (gs : List Gate) :
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) →
    (∀ g ∈ gs, Binary g → p ∉ g.inputs) →
    UniqueNot gs →
    ∀ w w' : List Bool, p < w.length → w.getD p false = true →
      Off (fun j => j = p) Eq w w' →
      Off (fun j => j = p) (fun a b => a = true → b = true)
        (gs.foldl step w) (gs.foldl step w') := by
  induction gs with
  | nil =>
    intro ops safe hu w w' hp ht he
    exact offEqImp he
  | cons g gs ih =>
    intro ops safe hu w w' hp ht he
    have opsTail : ∀ k ∈ gs, k.op = GateOp.and ∨ k.op = GateOp.or ∨ k.op = GateOp.not :=
      fun k hk => ops k (List.mem_cons_of_mem _ hk)
    have safeTail : ∀ k ∈ gs, Binary k → p ∉ k.inputs :=
      fun k hk => safe k (List.mem_cons_of_mem _ hk)
    have huTail := uniqueNotTail hu
    by_cases hn : g.op = GateOp.not
    · have tailBinary : ∀ k ∈ gs, Binary k := by
        intro k hk
        rcases opsTail k hk with ha | ho | hnot
        · exact Or.inl ha
        · exact Or.inr ho
        · obtain ⟨i, hi, hki⟩ := tailIndex g gs hk
          have hin : ((g :: gs).get i).op = GateOp.not := by rw [hki, hnot]
          let first : Fin (g :: gs).length := ⟨0, by simp⟩
          have hfn : ((g :: gs).get first).op = GateOp.not := hn
          have hif := hu i first hin hfn
          exact (hi (congrArg Fin.val hif)).elim
      have hgate :
          g.op.eval (g.inputs.map fun j => w.getD j false) = true →
          g.op.eval (g.inputs.map fun j => w'.getD j false) = true := by
        cases hargs : g.inputs with
        | nil => simp [hn, hargs, GateOp.eval]
        | cons j js =>
          by_cases hj : j = p
          · subst j
            simp only [List.getD_eq_getElem?_getD] at ht
            simp [hn, hargs, GateOp.eval, ht]
          · have hval := he.2 j hj
            simp only [List.getD_eq_getElem?_getD] at hval
            simp [hn, hargs, GateOp.eval, hval]
      have keep : ∀ k ∈ gs, ∀ a b : List Bool,
          Off (fun j => j = p) (fun u v => u = true → v = true) a b →
          (k.op.eval (k.inputs.map fun j => a.getD j false) = true →
            k.op.eval (k.inputs.map fun j => b.getD j false) = true) := by
        intro k hk a b hab
        apply binaryMono k (tailBinary k hk) _ hab
        intro j hj hbad
        exact safeTail k hk (tailBinary k hk) (hbad ▸ hj)
      change Off (fun j => j = p) (fun a b => a = true → b = true)
        (gs.foldl step (step w g)) (gs.foldl step (step w' g))
      exact offFold gs keep _ _ (offSnoc (offEqImp he) hgate)
    · have hb : Binary g := by
        rcases ops g List.mem_cons_self with ha | ho | hnot
        · exact Or.inl ha
        · exact Or.inr ho
        · exact (hn hnot).elim
      have hsafe : p ∉ g.inputs := safe g List.mem_cons_self hb
      have hgate : g.op.eval (g.inputs.map fun j => w.getD j false) =
          g.op.eval (g.inputs.map fun j => w'.getD j false) := by
        apply congrArg g.op.eval
        apply List.map_congr_left
        intro j hj
        apply he.2 j
        intro hbad
        exact hsafe (hbad ▸ hj)
      have hp' : p < (step w g).length := by simp [step]; omega
      have ht' : (step w g).getD p false = true := by
        unfold step
        rw [List.getD_append _ _ _ _ hp]
        exact ht
      change Off (fun j => j = p) (fun a b => a = true → b = true)
        (gs.foldl step (step w g)) (gs.foldl step (step w' g))
      exact ih opsTail safeTail huTail _ _ hp' ht' (offSnoc he hgate)

end PEqualNP.Outside.L_meta_1356_aux

theorem PEqualNP.Outside.L_meta_1356 : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)), (∀ i9 : Fin m, 2 ≤ (S i9).card) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ (o : Fin m) (x : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out o⟩ (List.ofFn x) = decide (∃ v ∈ S o, x v = true)) → ∀ ι : Fin 1 → Fin gates.length, (∀ q : Fin gates.length, (gates.get q).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ r : Fin 1, ι r = q) → ∀ (p : Fin n) (i0 : Fin m), p ∈ S i0 → ∃ a : Fin gates.length, ((gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ p.val ∈ (gates.get a).inputs := by
  classical
  open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_1356_aux in
  intro n m S hcard gates out ops correct pick atMostOne p i0 hp
  by_contra noReadWitness
  have safe : ∀ g ∈ gates, Binary g → p.val ∉ g.inputs := by
    intro g hg hb hread
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hg
    obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp hj
    let a : Fin gates.length := ⟨j, hlt⟩
    have ha : gates.get a = g := heq
    apply noReadWitness
    refine ⟨a, ?_, ?_⟩
    · rw [ha]
      exact hb
    · rw [ha]
      exact hread
  have hu : UniqueNot gates := by
    intro i j hi hj
    exact uniqueNeg pick atMostOne hi hj
  let x : Fin n → Bool := fun i => decide (i = p)
  let y : Fin n → Bool := fun _ => false
  have initial : Off (fun j => j = p.val) Eq (List.ofFn x) (List.ofFn y) := by
    apply offInput _ rfl
    intro i hi
    have hip : i ≠ p := fun e => hi (congrArg Fin.val e)
    simp [x, y, hip]
  have hpLen : p.val < (List.ofFn x).length := by simpa using p.isLt
  have hpTrue : (List.ofFn x).getD p.val false = true := by simp [x]
  have result := oneNotFold p.val gates (fun g hg => (ops g hg).1) safe hu
    (List.ofFn x) (List.ofFn y) hpLen hpTrue initial
  have outGE := outputNotInput S hcard gates out correct i0
  have ho : ¬ (out i0 = p.val) := by have := p.isLt; omega
  have comparison := result.2 (out i0) ho
  change (Circuit.eval ⟨gates, out i0⟩ (List.ofFn x) = true →
    Circuit.eval ⟨gates, out i0⟩ (List.ofFn y) = true) at comparison
  rw [correct, correct] at comparison
  have hx : ∃ v ∈ S i0, x v = true := ⟨p, hp, by simp [x]⟩
  simp [hx, y] at comparison
