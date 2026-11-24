import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1660

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma getD_snoc {α : Type} (L : List α) (a d : α) (w : ℕ) :
    (L ++ [a]).getD w d = if w < L.length then L.getD w d else if w = L.length then a else d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_append_right (by omega)]
    rw [List.getElem?_eq_none (by simp; omega)]; simp

-- one step of evaluation and one step of the dependency sets
def wstep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def dstep (D : List (Finset ℕ)) (g : Gate) : List (Finset ℕ) :=
  D ++ [g.inputs.toFinset.biUnion fun i => D.getD i ∅]

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl wstep x := rfl

lemma sem (P : ℕ → Prop) : ∀ (gs : List Gate) (W1 W2 : List Bool) (D : List (Finset ℕ)),
    W1.length = D.length → W2.length = D.length →
    (∀ w, (∀ i ∈ D.getD w ∅, P i) → W1.getD w false = W2.getD w false) →
    ∀ w, (∀ i ∈ (gs.foldl dstep D).getD w ∅, P i) →
      (gs.foldl wstep W1).getD w false = (gs.foldl wstep W2).getD w false := by
  intro gs
  induction gs with
  | nil => intro W1 W2 D _ _ h; simpa using h
  | cons g gs ih =>
    intro W1 W2 D h1 h2 h
    simp only [List.foldl_cons]
    apply ih
    · simp [wstep, dstep, h1]
    · simp [wstep, dstep, h2]
    · intro w hw
      simp only [wstep, dstep] at hw ⊢
      rw [getD_snoc, getD_snoc]
      rw [getD_snoc] at hw
      rw [h1, h2]
      split_ifs with c1 c2
      · rw [ite_eq_left c1] at hw; exact h w hw
      · rw [ite_eq_right c1, ite_eq_left c2] at hw
        congr 1
        apply List.map_congr_left
        intro j hj
        apply h j
        intro i hi
        apply hw
        rw [Finset.mem_biUnion]
        exact ⟨j, List.mem_toFinset.mpr hj, hi⟩
      · rfl

lemma cardb : ∀ (gs : List Gate) (D : List (Finset ℕ)) (k : ℕ),
    (∀ g ∈ gs, g.inputs.length ≤ 2) →
    (∀ T : Finset ℕ, (T.biUnion fun w => D.getD w ∅).card ≤ T.card + k) →
    ∀ T : Finset ℕ, (T.biUnion fun w => (gs.foldl dstep D).getD w ∅).card ≤
      T.card + k + gs.length := by
  intro gs
  induction gs with
  | nil => intro D k _ h T; simpa using h T
  | cons g gs ih =>
    intro D k hg h T
    simp only [List.foldl_cons, List.length_cons]
    have := ih (dstep D g) (k + 1) (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg')) ?_ T
    · omega
    intro T
    have hsub : (T.biUnion fun w => (dstep D g).getD w ∅) ⊆
        ((T.erase D.length) ∪ g.inputs.toFinset).biUnion fun w => D.getD w ∅ := by
      intro i hi
      rw [Finset.mem_biUnion] at hi
      obtain ⟨w, hw, hi⟩ := hi
      simp only [dstep] at hi
      rw [getD_snoc] at hi
      rw [Finset.mem_biUnion]
      split_ifs at hi with c1 c2
      · exact ⟨w, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨by omega, hw⟩), hi⟩
      · rw [Finset.mem_biUnion] at hi
        obtain ⟨j, hj, hi⟩ := hi
        exact ⟨j, Finset.mem_union_right _ hj, hi⟩
      · simp at hi
    have hc := h ((T.erase D.length) ∪ g.inputs.toFinset)
    have h3 := Finset.card_union_le (T.erase D.length) g.inputs.toFinset
    have h4 := List.toFinset_card_le g.inputs
    have h5 := hg g List.mem_cons_self
    have h6 := Finset.card_le_card hsub
    by_cases hm : D.length ∈ T
    · have h7 := Finset.card_erase_of_mem hm
      have h8 : 1 ≤ T.card := Finset.card_pos.mpr ⟨_, hm⟩
      omega
    · have h9 : (T.biUnion fun w => (dstep D g).getD w ∅) =
          T.biUnion fun w => D.getD w ∅ := by
        apply Finset.biUnion_congr rfl
        intro w hw
        simp only [dstep]
        rw [getD_snoc]
        have : w ≠ D.length := fun e => hm (e ▸ hw)
        split_ifs with c1
        · rfl
        · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
      rw [h9]; have := h T; omega

lemma base_card (n : ℕ) (T : Finset ℕ) :
    (T.biUnion fun w => ((List.range n).map fun i => ({i} : Finset ℕ)).getD w ∅).card ≤
      T.card + 0 := by
  refine le_trans Finset.card_biUnion_le ?_
  rw [Nat.add_zero]
  calc (∑ w ∈ T, (((List.range n).map fun i => ({i} : Finset ℕ)).getD w ∅).card)
      ≤ ∑ w ∈ T, 1 := by
        apply Finset.sum_le_sum
        intro w _
        rw [List.getD_eq_getElem?_getD]
        by_cases hw : w < n
        · simp [hw]
        · rw [List.getElem?_eq_none (by simp; omega)]; simp
    _ = T.card := by simp

lemma fanin_lower_bound (n : ℕ) (C : Circuit)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hdep : ∀ i : Fin n, ∃ x y : Fin n → Bool,
      (∀ j : Fin n, j ≠ i → x j = y j) ∧
      PEqualNP.MetaComplexity.circuitFun n C x ≠
        PEqualNP.MetaComplexity.circuitFun n C y) : n ≤ C.size + 1 := by
  let D0 : List (Finset ℕ) := (List.range n).map fun i => ({i} : Finset ℕ)
  let S := (C.gates.foldl dstep D0).getD C.output ∅
  have hsub : Finset.range n ⊆ S := by
    intro i hi
    rw [Finset.mem_range] at hi
    by_contra hni
    obtain ⟨x, y, hagree, hne⟩ := hdep ⟨i, hi⟩
    apply hne
    have key := sem (fun j => (List.ofFn x).getD j false = (List.ofFn y).getD j false)
      C.gates (List.ofFn x) (List.ofFn y) D0
      (by simp [D0]) (by simp [D0]) ?_ C.output ?_
    · unfold PEqualNP.MetaComplexity.circuitFun Circuit.eval
      rw [wires_eq, wires_eq]
      exact key
    · intro w hw
      by_cases hwn : w < n
      · apply hw w
        simp [D0, List.getD_eq_getElem?_getD, hwn]
      · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
    · intro j hj
      have hji : j ≠ i := fun e => hni (e ▸ hj)
      by_cases hjn : j < n
      · simpa [List.getD_eq_getElem?_getD, hjn] using
          hagree ⟨j, hjn⟩ (by intro e; apply hji; exact congrArg Fin.val e)
      · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
  have hc := cardb C.gates D0 0 hfan (base_card n) {C.output}
  simp only [Finset.singleton_biUnion, Finset.card_singleton] at hc
  have := Finset.card_le_card hsub
  rw [Finset.card_range] at this
  change n ≤ ((C.gates.foldl dstep D0).getD C.output ∅).card at this
  unfold Circuit.size
  omega

lemma incidence_essential (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hcard : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hpair : ∀ pa pb : Fin N, pa ≠ pb → ∃! l : Fin N, I pa l ∧ I pb l)
    (haccept : ∀ p l : Fin N, I p l → circuitFun (N + N) C
      (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)) = true)
    (hsound : ∀ z : Fin (N + N) → Bool,
      (Finset.univ.filter (fun l : Fin N => z (Fin.natAdd N l) = true)).card ≤ q →
      (¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
      circuitFun (N + N) C z = false) :
    ∀ i : Fin (N + N), ∃ x y : Fin (N + N) → Bool,
      (∀ j, j ≠ i → x j = y j) ∧ circuitFun (N + N) C x ≠ circuitFun (N + N) C y := by
  classical
  have hcross : ∀ p l : Fin N, Fin.castAdd N p ≠ Fin.natAdd N l := by
    intro p l he
    have h := congrArg Fin.val he
    change p.val = N + l.val at h
    omega
  have hpoint : ∀ p : Fin N, ∃ l : Fin N, I p l := by
    intro p
    let p' : Fin N := ⟨if p.val = 0 then 1 else 0, by split <;> omega⟩
    have hne : p ≠ p' := by
      intro he
      have h := congrArg Fin.val he
      change p.val = (if p.val = 0 then 1 else 0) at h
      split_ifs at h <;> omega
    obtain ⟨l, hl, _⟩ := hpair p p' hne
    exact ⟨l, hl.1⟩
  have hline : ∀ l : Fin N, ∃ p : Fin N, I p l := by
    intro l
    have hn : (Finset.univ.filter (fun p => I p l)).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro he
      have hc := hcard l
      rw [he, Finset.card_empty] at hc
      omega
    obtain ⟨p, hp⟩ := hn
    exact ⟨p, (Finset.mem_filter.mp hp).2⟩
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro p
    obtain ⟨l, hil⟩ := hpoint p
    let x : Fin (N + N) → Bool := fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)
    let y : Fin (N + N) → Bool := fun k => decide (k = Fin.natAdd N l)
    refine ⟨x, y, ?_, ?_⟩
    · intro j hj
      simp only [x, y, hj, false_or]
    · have hx : circuitFun (N + N) C x = true := haccept p l hil
      have hy : circuitFun (N + N) C y = false := by
        apply hsound
        · have he : (Finset.univ.filter (fun l' : Fin N => y (Fin.natAdd N l') = true)) = {l} := by
            ext l'
            simp [y, Fin.ext_iff]
          rw [he, Finset.card_singleton]
          omega
        · rintro ⟨p', l', _, hp', _⟩
          exact hcross p' l (of_decide_eq_true hp')
      rw [hx, hy]
      decide
  · intro l
    obtain ⟨p, hil⟩ := hline l
    let x : Fin (N + N) → Bool := fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)
    let y : Fin (N + N) → Bool := fun k => decide (k = Fin.castAdd N p)
    refine ⟨x, y, ?_, ?_⟩
    · intro j hj
      simp only [x, y, hj, or_false]
    · have hx : circuitFun (N + N) C x = true := haccept p l hil
      have hy : circuitFun (N + N) C y = false := by
        apply hsound
        · have he : (Finset.univ.filter (fun l' : Fin N => y (Fin.natAdd N l') = true)) = ∅ := by
            ext l'
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
              iff_false, y, decide_eq_true_eq]
            exact (hcross p l').symm
          rw [he, Finset.card_empty]
          omega
        · rintro ⟨p', l', _, _, hl'⟩
          exact (hcross p l').symm (of_decide_eq_true hl')
      rw [hx, hy]
      decide

end PEqualNP.Outside.L_meta_1660

open PEqualNP.Outside.L_meta_1660

theorem PEqualNP.Outside.L_meta_1660 : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, (Finset.univ.filter (fun p0 => I p0 l)).card = q + 1) → (∀ pa pb : Fin N, pa ≠ pb → ∃! l0 : Fin N, I pa l0 ∧ I pb l0) → PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C → (∀ p1 l1 : Fin N, I p1 l1 → PEqualNP.MetaComplexity.circuitFun (N + N) C (fun k1 => decide (k1 = Fin.castAdd N p1 ∨ k1 = Fin.natAdd N l1)) = true) → (∀ z1 : Fin (N + N) → Bool, (Finset.univ.filter (fun l1b : Fin N => z1 (Fin.natAdd N l1b) = true)).card ≤ q → (¬ ∃ p1c l1c : Fin N, I p1c l1c ∧ z1 (Fin.castAdd N p1c) = true ∧ z1 (Fin.natAdd N l1c) = true) → PEqualNP.MetaComplexity.circuitFun (N + N) C z1 = false) → 2 * N ≤ C.size + 1 := by
  intro q N I _ C hq hN hcard hpair hmono _ haccept hsound
  have hbound := fanin_lower_bound (N + N) C
    (fun g hg => (hmono g hg).2)
    (incidence_essential q N I C hq hN hcard hpair haccept hsound)
  omega
