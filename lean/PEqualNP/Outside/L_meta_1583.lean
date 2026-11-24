import Mathlib

namespace PEqualNP.Outside.L_meta_1583

lemma exists_rotor {N : ℕ} (T : Finset (Fin N)) :
    ∃ sigma : Fin N → Fin N, (∀ x ∈ T, sigma x ∈ T) ∧ Set.InjOn sigma ↑T ∧
      (∀ x ∈ T, ∀ y ∈ T, ∃ k : ℕ, sigma^[k] x = y) := by
  obtain ⟨sigma, hcycle, _⟩ := Finset.exists_cycleOn T
  refine ⟨sigma, hcycle.1.1, hcycle.1.2.1, ?_⟩
  intro x hx y hy
  obtain ⟨k, _, hk⟩ := hcycle.exists_pow_eq hx hy
  exact ⟨k, by simpa only [Equiv.Perm.coe_pow] using hk⟩

lemma rotor_ne_two {N : ℕ} (T : Finset (Fin N)) (hcard : 3 ≤ T.card)
    (sigma : Fin N → Fin N)
    (htrans : ∀ x ∈ T, ∀ y ∈ T, ∃ k : ℕ, sigma^[k] x = y)
    {x : Fin N} (hx : x ∈ T) : sigma (sigma x) ≠ x := by
  intro htwo
  have hiter : ∀ k : ℕ, sigma^[k] x ∈ ({x, sigma x} : Finset (Fin N)) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      simp only [Finset.mem_insert, Finset.mem_singleton] at ih ⊢
      rcases ih with ih | ih
      · exact Or.inr (congrArg sigma ih)
      · exact Or.inl ((congrArg sigma ih).trans htwo)
  have hsub : T ⊆ {x, sigma x} := by
    intro y hy
    obtain ⟨k, hk⟩ := htrans x hx y hy
    exact hk ▸ hiter k
  have hle := Finset.card_le_card hsub
  have hpair : ({x, sigma x} : Finset (Fin N)).card ≤ 2 := by
    exact le_trans (Finset.card_insert_le _ _) (by simp)
  omega

lemma line_meet {N : ℕ} (L : Fin N → Finset (Fin N)) (i0 : Fin N)
    (hi : ∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1)
    (s : Fin N) (hs : s ≠ i0) :
    ∃ a : Fin N, a ∈ L i0 ∧ a ∈ L s ∧
      ∀ b : Fin N, b ∈ L i0 → b ∈ L s → b = a := by
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp (hi s i0 hs)
  have ham : a ∈ L s ∩ L i0 := by rw [ha]; simp
  refine ⟨a, (Finset.mem_inter.mp ham).2, (Finset.mem_inter.mp ham).1, ?_⟩
  intro b hb0 hbs
  have hb : b ∈ L s ∩ L i0 := Finset.mem_inter.mpr ⟨hbs, hb0⟩
  simpa [ha] using hb

lemma rotor_geometry {N : ℕ} (L : Fin N → Finset (Fin N)) (i0 : Fin N)
    (T0 : Finset (Fin N))
    (hi : ∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1)
    (hsub : T0 ⊆ L i0)
    (sigma : Fin N → Fin N) (x0 : Fin N) (B : Fin N → Fin N → Finset (Fin N))
    (hpres : ∀ x ∈ T0, sigma x ∈ T0)
    (hshort : ∀ x ∈ T0, sigma (sigma x) ≠ x)
    (hx0 : x0 ∈ T0)
    (hcore : ∀ s : Fin N, s ≠ i0 → ∀ p ∈ L s, ∀ x ∈ T0, x ∈ L s →
      B s p = if p = x then (∅ : Finset (Fin N)) else {sigma x})
    (hother : ∀ s : Fin N, s ≠ i0 → ∀ r ∈ L i0 \ T0, r ∈ L s →
      ∀ p ∈ L s, B s p = {x0}) :
    (∀ s : Fin N, s ≠ i0 → ∀ p ∈ L s,
      B s p ∩ L s = ∅ ∧
      ((∃ v ∈ T0, (fun v : Fin N => decide (v = p ∨ v ∈ B s p)) v = true) ∨
        ∀ v : Fin N, v ∉ L i0 →
          (fun v : Fin N => decide (v = p ∨ v ∈ B s p)) v = true) ∧
      ∀ v ∈ L s, decide (v = p ∨ v ∈ B s p) = true ↔ v = p) ∧
    (∀ s s' : Fin N, s ≠ i0 → s' ≠ i0 → s ≠ s' →
      ¬ ((∃ p ∈ L s \ L s', (B s p ∩ L s').Nonempty) ∧
        (∃ p ∈ L s' \ L s, (B s' p ∩ L s).Nonempty))) := by
  have hfixed : ∀ x ∈ T0, sigma x ≠ x := by
    intro x hx he
    apply hshort x hx
    rw [he, he]
  have bprop : ∀ s : Fin N, s ≠ i0 → ∀ p ∈ L s,
      ∃ a : Fin N, a ∈ L i0 ∧ a ∈ L s ∧
        (∀ b : Fin N, b ∈ L i0 → b ∈ L s → b = a) ∧
        (∀ v ∈ B s p, v ∈ T0 ∧ v ≠ a ∧ (a ∈ T0 → v = sigma a)) ∧
        (∃ v ∈ T0, v = p ∨ v ∈ B s p) := by
    intro s hs p hp
    obtain ⟨a, ha0, has, huniq⟩ := line_meet L i0 hi s hs
    refine ⟨a, ha0, has, huniq, ?_⟩
    by_cases ha : a ∈ T0
    · rw [hcore s hs p hp a ha has]
      by_cases hpa : p = a
      · simp only [hpa, ite_true, Finset.notMem_empty, IsEmpty.forall_iff ]
        exact ⟨by simp, a, ha, Or.inl rfl⟩
      · simp only [hpa, ite_false, Finset.mem_singleton]
        refine ⟨?_, sigma a, hpres a ha, Or.inr rfl⟩
        intro v hv
        subst v
        exact ⟨hpres a ha, hfixed a ha, fun _ => rfl⟩
    · rw [hother s hs a (Finset.mem_sdiff.mpr ⟨ha0, ha⟩) has p hp]
      refine ⟨?_, x0, hx0, Or.inr (Finset.mem_singleton_self x0)⟩
      intro v hv
      have hvx : v = x0 := Finset.mem_singleton.mp hv
      subst v
      exact ⟨hx0, fun h => ha (h ▸ hx0), fun h => (ha h).elim⟩
  constructor
  · intro s hs p hp
    obtain ⟨a, ha0, has, huniq, hb, hv⟩ := bprop s hs p hp
    have hdis : B s p ∩ L s = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro v hv
      obtain ⟨hvb, hvs⟩ := Finset.mem_inter.mp hv
      exact (hb v hvb).2.1 (huniq v (hsub (hb v hvb).1) hvs)
    refine ⟨hdis, Or.inl ?_, ?_⟩
    · obtain ⟨v, hvt, hv⟩ := hv
      exact ⟨v, hvt, by simpa using hv⟩
    · intro v hvs
      simp only [decide_eq_true_eq]
      constructor
      · rintro (he | hvb)
        · exact he
        · have hvint : v ∈ B s p ∩ L s := Finset.mem_inter.mpr ⟨hvb, hvs⟩
          rw [hdis] at hvint
          exact (Finset.notMem_empty v hvint).elim
      · exact Or.inl
  · intro s s' hs hs' hss' hconf
    obtain ⟨⟨p, hp, z, hz⟩, ⟨p', hp', z', hz'⟩⟩ := hconf
    obtain ⟨a, ha0, has, huniqa, hba, hva⟩ :=
      bprop s hs p (Finset.mem_sdiff.mp hp).1
    obtain ⟨b, hb0, hbs, huniqb, hbb, hvb⟩ :=
      bprop s' hs' p' (Finset.mem_sdiff.mp hp').1
    obtain ⟨hzb, hzs⟩ := Finset.mem_inter.mp hz
    obtain ⟨hz'b, hz's⟩ := Finset.mem_inter.mp hz'
    have hzt : z ∈ T0 := (hba z hzb).1
    have hz't : z' ∈ T0 := (hbb z' hz'b).1
    have hza : z' = a := huniqa z' (hsub hz't) hz's
    have hzb' : z = b := huniqb z (hsub hzt) hzs
    have hat : a ∈ T0 := hza ▸ hz't
    have hbt : b ∈ T0 := hzb' ▸ hzt
    have hsigab : sigma a = b := ((hba z hzb).2.2 hat).symm.trans hzb'
    have hsigba : sigma b = a := ((hbb z' hz'b).2.2 hbt).symm.trans hza
    exact hshort a hat (by rw [hsigab, hsigba])

end PEqualNP.Outside.L_meta_1583

open PEqualNP.Outside.L_meta_1583

theorem PEqualNP.Outside.L_meta_1583 : ∀ (q m N : ℕ) (L : Fin N → Finset (Fin N)) (i0 : Fin N) (T0 : Finset (Fin N)),
    3 ≤ q → 3 ≤ m → m ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    T0 ⊆ L i0 → T0.card = m →
    (∃ sigma : Fin N → Fin N, (∀ x ∈ T0, sigma x ∈ T0) ∧ Set.InjOn sigma ↑T0 ∧ (∀ x ∈ T0, ∀ y ∈ T0, ∃ k : ℕ, sigma^[k] x = y)) ∧
    ∀ (sigma : Fin N → Fin N) (x0 : Fin N) (B : Fin N → Fin N → Finset (Fin N)),
    (∀ x ∈ T0, sigma x ∈ T0) ∧ Set.InjOn sigma ↑T0 ∧ (∀ x ∈ T0, ∀ y ∈ T0, ∃ k : ℕ, sigma^[k] x = y) → x0 ∈ T0 →
    (∀ s : Fin N, s ≠ i0 → ∀ p ∈ L s, ∀ x ∈ T0, x ∈ L s → B s p = if p = x then (∅ : Finset (Fin N)) else {sigma x}) →
    (∀ s : Fin N, s ≠ i0 → ∀ r ∈ L i0 \ T0, r ∈ L s → ∀ p ∈ L s, B s p = {x0}) →
    (∀ s : Fin N, s ≠ i0 → ∀ p ∈ L s, B s p ∩ L s = ∅ ∧ ((∃ v ∈ T0, (fun v : Fin N => decide (v = p ∨ v ∈ B s p)) v = true) ∨ ∀ v : Fin N, v ∉ L i0 → (fun v : Fin N => decide (v = p ∨ v ∈ B s p)) v = true) ∧
      ∀ v ∈ L s, decide (v = p ∨ v ∈ B s p) = true ↔ v = p) ∧
    (∀ s s' : Fin N, s ≠ i0 → s' ≠ i0 → s ≠ s' → ¬ ((∃ p ∈ L s \ L s', (B s p ∩ L s').Nonempty) ∧ (∃ p ∈ L s' \ L s, (B s' p ∩ L s).Nonempty))) := by
  intro q m N L i0 T0 _ hm _ _ _ hmeet _ hsub hcard
  refine ⟨exists_rotor T0, ?_⟩
  intro sigma x0 B hs hx0 hcore hother
  apply rotor_geometry L i0 T0 hmeet hsub sigma x0 B hs.1 ?_ hx0 hcore hother
  intro x hx
  exact rotor_ne_two T0 (by omega) sigma hs.2.2 hx
