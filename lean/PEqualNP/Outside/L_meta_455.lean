import Mathlib

theorem PEqualNP.Outside.L_meta_455 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    (∀ a b c : Fin n, ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c a)) →
    (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) →
    ∀ u v : Fin n, G.Adj u v →
      (∀ a ∈ Finset.univ.filter (fun w => G.Adj v w),
        ∀ b ∈ Finset.univ.filter (fun w => G.Adj v w), ¬ G.Adj a b) ∧
      (∀ a ∈ Finset.univ.filter (fun w => G.Adj u w),
        ∀ b ∈ Finset.univ.filter (fun w => G.Adj u w), ¬ G.Adj a b) ∧
      (∀ a ∈ Finset.univ.filter (fun w => G.Adj v w ∧ w ≠ u) ∪
              Finset.univ.filter (fun w => G.Adj u w ∧ w ≠ v),
        ∀ b ∈ Finset.univ.filter (fun w => G.Adj v w ∧ w ≠ u) ∪
              Finset.univ.filter (fun w => G.Adj u w ∧ w ≠ v), ¬ G.Adj a b) := by
  intro n G _ htri hsq u v huv
  constructor
  · intro a ha b hb hab
    exact htri v a b ⟨(Finset.mem_filter.mp ha).2, hab,
      (Finset.mem_filter.mp hb).2.symm⟩
  constructor
  · intro a ha b hb hab
    exact htri u a b ⟨(Finset.mem_filter.mp ha).2, hab,
      (Finset.mem_filter.mp hb).2.symm⟩
  · intro a ha b hb hab
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    rcases ha with ⟨hva, hau⟩ | ⟨hua, hav⟩
    · rcases hb with ⟨hvb, hbu⟩ | ⟨hub, hbv⟩
      · exact htri v a b ⟨hva, hab, hvb.symm⟩
      · exact hsq u v a b hau.symm hbv.symm ⟨huv, hva, hab, hub.symm⟩
    · rcases hb with ⟨hvb, hbu⟩ | ⟨hub, hbv⟩
      · exact hsq v u a b hav.symm hbu.symm ⟨huv.symm, hua, hab, hvb.symm⟩
      · exact htri u a b ⟨hua, hab, hub.symm⟩
