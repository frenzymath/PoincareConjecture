import PoincareConjecture.Proofs.M47.PositiveHistoryFlow










set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M47Positive

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]




theorem exists_closed_flow_of_initial_overlap
    {a b c : ℝ} (hac : a < c) (hcb : c ≤ b)
    (F0 : RicciFlow n M (Icc a c)) (F1 : RicciFlow n M (Ioc a b))
    (hmetric : ∀ t ∈ Ioc a c, F0.metric t = F1.metric t) :
    ∃ G : RicciFlow n M (Icc a b),
      (∀ t ∈ Icc a c, G.metric t = F0.metric t) ∧
      (∀ t ∈ Ioc a b, G.metric t = F1.metric t) := by
  classical
  let g (t : ℝ) := if t ≤ a then F0.metric t else F1.metric t
  let D (t : ℝ) : LeviCivitaData (g t) := by
    dsimp only [g]
    split_ifs
    · exact F0.connection t
    · exact F1.connection t
  have hg0 (t : ℝ) (ht : t ∈ Icc a c) : g t = F0.metric t := by
    dsimp only [g]
    split_ifs with hta
    · rfl
    · exact (hmetric t ⟨lt_of_not_ge hta, ht.2⟩).symm
  have hg1 (t : ℝ) (ht : t ∈ Ioc a b) : g t = F1.metric t :=
    if_neg (not_le_of_gt ht.1)
  have hricci {g₀ g₁ : RiemannianMetric n M} (D₀ : LeviCivitaData g₀)
      (D₁ : LeviCivitaData g₁) (heq : g₀ = g₁) (x : M)
      (v w : TangentSpace (𝓡 n) x) : D₀.ricci x v w = D₁.ricci x v w := by
    subst g₁
    have h := D₀.ricci_eq_of_local_isometry D₁ (f := id) isOpen_univ
        contMDiff_id.contMDiffOn
        (fun _ _ _ _ => by simp only [mfderiv_id]; rfl)
        (mem_univ x) v w
    simp only [mfderiv_id] at h
    convert h using 1
    rfl
  have hsm0 : RiemannianMetric.IsSmoothFamilyOn g (Icc a c) := by
    apply F0.smooth.congr
    intro p hp
    rw [hg0 p.1 hp.1]
  have hsm1 : RiemannianMetric.IsSmoothFamilyOn g (Ioc a b) := by
    apply F1.smooth.congr
    intro p hp
    rw [hg1 p.1 hp.1]
  have hsmooth : RiemannianMetric.IsSmoothFamilyOn g (Icc a b) := by
    intro p hp
    by_cases hpa : p.1 ≤ a
    · have hpc : p.1 < c := hpa.trans_lt hac
      apply (hsm0 p ⟨⟨hp.1.1, hpc.le⟩, hp.2⟩).mono_of_mem_nhdsWithin
      have hn : ∀ᶠ q : ℝ × M in 𝓝 p, q.1 < c :=
        continuous_fst.continuousAt.eventually (Iio_mem_nhds hpc)
      filter_upwards [self_mem_nhdsWithin,
        Filter.Eventually.filter_mono nhdsWithin_le_nhds hn] with q hq hqc
      exact ⟨⟨hq.1.1, hqc.le⟩, hq.2⟩
    · have hap : a < p.1 := lt_of_not_ge hpa
      apply (hsm1 p ⟨⟨hap, hp.1.2⟩, hp.2⟩).mono_of_mem_nhdsWithin
      have hn : ∀ᶠ q : ℝ × M in 𝓝 p, a < q.1 :=
        continuous_fst.continuousAt.eventually (Ioi_mem_nhds hap)
      filter_upwards [self_mem_nhdsWithin,
        Filter.Eventually.filter_mono nhdsWithin_le_nhds hn] with q hq haq
      exact ⟨⟨haq, hq.1.2⟩, hq.2⟩
  have hequation (t : ℝ) (ht : t ∈ Icc a b) (x : M)
      (v w : TangentSpace (𝓡 n) x) :
      HasDerivWithinAt (fun s => (g s).inner x v w)
        (-2 * (D t).ricci x v w) (Icc a b) t := by
    by_cases hta : t ≤ a
    · have htaeq : t = a := le_antisymm hta ht.1
      subst t
      have hder : HasDerivWithinAt (fun s => (g s).inner x v w)
          (-2 * (F0.connection a).ricci x v w) (Icc a c) a := by
        apply (F0.equation a ⟨le_rfl, hac.le⟩ x v w).congr_of_mem
        · intro s hs
          rw [hg0 s hs]
        · exact ⟨le_rfl, hac.le⟩
      have hnear : Icc a c ∈ 𝓝[Icc a b] a := by
        filter_upwards [self_mem_nhdsWithin,
          Filter.Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds hac)] with s hs hsc
        exact ⟨hs.1, hsc.le⟩
      rw [hricci (D a) (F0.connection a) (hg0 a ⟨le_rfl, hac.le⟩)]
      exact hder.mono_of_mem_nhdsWithin hnear
    · have hat : a < t := lt_of_not_ge hta
      have hder : HasDerivWithinAt (fun s => (g s).inner x v w)
          (-2 * (F1.connection t).ricci x v w) (Ioc a b) t := by
        apply (F1.equation t ⟨hat, ht.2⟩ x v w).congr_of_mem
        · intro s hs
          rw [hg1 s hs]
        · exact ⟨hat, ht.2⟩
      have hnear : Ioc a b ∈ 𝓝[Icc a b] t := by
        filter_upwards [self_mem_nhdsWithin,
          Filter.Eventually.filter_mono nhdsWithin_le_nhds (Ioi_mem_nhds hat)] with s hs has
        exact ⟨has, hs.2⟩
      rw [hricci (D t) (F1.connection t) (hg1 t ⟨hat, ht.2⟩)]
      exact hder.mono_of_mem_nhdsWithin hnear
  let G : RicciFlow n M (Icc a b) :=
    { metric := g
      connection := D
      interval := ordConnected_Icc
      nontrivial := ⟨a, ⟨le_rfl, hac.le.trans hcb⟩,
        b, ⟨hac.le.trans hcb, le_rfl⟩, (hac.trans_le hcb).ne⟩
      smooth := hsmooth
      equation := hequation }
  exact ⟨G, hg0, hg1⟩

end PoincareConjecture.M47Positive
