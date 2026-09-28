import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CapExcursionSubarcs
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.NeckShortening











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.CapCertificate

open M28

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}




theorem exists_core_excursion_replacement (N : CapCertificate g)
    (hepsilon : N.epsilon ≤ neckShorteningEpsilon)
    {U : Set M} (hNU : N.carrier ⊆ U)
    {γ : ℝ → M} {a b t : ℝ} (ht : t ∈ Icc a b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc a b))
    (hγU : MapsTo γ (Icc a b) U)
    (hcore : γ t ∈ N.closed_core)
    (ha : γ a ∉ N.carrier) (hb : γ b ∉ N.carrier) :
    ∃ σ : ℝ → M, σ 0 = γ a ∧ σ 1 = γ b ∧
      ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 σ (Icc (0 : ℝ) 1) ∧
      MapsTo σ (Icc (0 : ℝ) 1) U ∧
      g.pathELength σ 0 1 +
          ENNReal.ofReal (N.end_neck.scale * N.epsilon⁻¹ / 8) ≤
        g.pathELength γ a b := by
  have hinv : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  have h0lo : -N.epsilon⁻¹ < 0 := neg_neg_of_pos hinv
  let W : Set M := N.closed_core ∪ N.end_neck.region (-N.epsilon⁻¹) 0
  have hWcap : W ⊆ N.carrier :=
    subset_closure.trans (N.open_precompact_recut h0lo hinv).2.2
  have haW : γ a ∉ W := fun h => ha (hWcap h)
  have hbW : γ b ∉ W := fun h => hb (hWcap h)
  have hleft : ContinuousOn γ (Icc a t) :=
    hγ.continuousOn.mono (Icc_subset_Icc le_rfl ht.2)
  have hreflect : ContinuousOn (fun s => γ (a + t - s)) (Icc a t) := by
    apply hleft.comp (continuous_const.sub continuous_id).continuousOn
    intro s hs
    change a ≤ a + t - s ∧ a + t - s ≤ t
    exact ⟨by linarith only [hs.2], by linarith only [hs.1]⟩
  obtain ⟨s₀, hs₀, hcross₀⟩ :=
    N.path_from_core_crosses_recut_sphere h0lo hinv ht.1 hreflect
      (by simpa only [add_sub_cancel_left] using hcore)
      (by simpa only [add_sub_cancel_right] using haW)
  let c : ℝ := a + t - s₀
  have hac : a ≤ c := by dsimp only [c]; linarith only [hs₀.2]
  have hct : c ≤ t := by dsimp only [c]; linarith only [hs₀.1]
  have hc : γ c ∈ N.end_neck.central_sphere := by
    rw [N.end_neck.central_sphere_eq]
    exact hcross₀
  obtain ⟨d, hd, hcrossd⟩ :=
    N.path_from_core_crosses_recut_sphere h0lo hinv ht.2
      (hγ.continuousOn.mono (Icc_subset_Icc ht.1 le_rfl)) hcore hbW
  have hdSphere : γ d ∈ N.end_neck.central_sphere := by
    rw [N.end_neck.central_sphere_eq]
    exact hcrossd
  let q : ℝ := -N.epsilon⁻¹ / 2
  have hqlo : -N.epsilon⁻¹ < q := by dsimp only [q]; linarith only [hinv]
  have hqzero : q < 0 := by dsimp only [q]; linarith only [hinv]
  obtain ⟨v, w, hcv, hvw, hwt, hvSphere, hwSphere, hslab⟩ :=
    N.exists_incoming_neck_subarc hqlo hqzero hct
      (hγ.continuousOn.mono (Icc_subset_Icc hac ht.2)) hc hcore
  have hqN : q ∈ Ioo (-N.end_neck.epsilon⁻¹) N.end_neck.epsilon⁻¹ := by
    rw [N.end_neck_epsilon]
    exact ⟨hqlo, hqzero.trans hinv⟩
  have hslabN : MapsTo γ (Icc v w) N.end_neck.carrier := by
    intro s hs
    obtain ⟨z, hz, hzmap⟩ := hslab hs
    rw [← hzmap]
    apply N.end_neck.coordinate_map_mem_of_axial z
    exact ⟨hqN.1.trans_le hz.2.1, hz.2.2.trans_lt
      (by simpa only [N.end_neck_epsilon] using hinv)⟩
  have hvzero : (N.end_neck.coordinate_inverse (γ v)).2 = 0 :=
    (N.end_neck.mem_central_sphere_iff_of_mem_carrier
      (N.end_neck.central_sphere_subset hvSphere)).mp hvSphere
  have hwq : (N.end_neck.coordinate_inverse (γ w)).2 = q := by
    obtain ⟨z, hz, hzmap⟩ := hwSphere
    have hzq : z.2 = q := hz.2
    rw [← hzmap, N.end_neck.coordinate_inverse_coordinate_map_of_axial z (hzq.symm ▸ hqN)]
    exact hzq
  have hheight : N.end_neck.epsilon⁻¹ / 2 ≤
      |(N.end_neck.coordinate_inverse (γ w)).2 -
        (N.end_neck.coordinate_inverse (γ v)).2| := by
    rw [hwq, hvzero, sub_zero, abs_of_neg hqzero, N.end_neck_epsilon]
    dsimp only [q]
    exact le_of_eq (by ring)
  have hNU' : N.end_neck.central_sphere ⊆ U :=
    N.end_neck.central_sphere_subset.trans (N.end_neck_subset.trans hNU)
  obtain ⟨σ, hσ0, hσ1, hσ, hσU, hsave⟩ :=
    exists_neck_excursion_replacement N.end_neck
      (by simpa only [N.end_neck_epsilon] using hepsilon) hNU'
      (hac.trans hcv) le_rfl hvw.le (hwt.trans hd.1) hd.2
      hγ hγU hvSphere hdSphere hslabN hheight
  refine ⟨σ, hσ0, hσ1, hσ, hσU, ?_⟩
  simpa only [N.end_neck_epsilon] using hsave




theorem endpoint_mem_of_intrinsic_minimizer (N : CapCertificate g)
    (hepsilon : N.epsilon ≤ neckShorteningEpsilon)
    {U : Set M} (hNU : N.carrier ⊆ U)
    {γ : ℝ → M} {a b t : ℝ} (ht : t ∈ Icc a b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc a b))
    (hγU : MapsTo γ (Icc a b) U)
    (hfinite : g.pathELength γ a b ≠ ⊤)
    (hmin : g.pathELength γ a b = intrinsicEDist g U (γ a) (γ b))
    (hcore : γ t ∈ N.closed_core) : γ a ∈ N.carrier ∨ γ b ∈ N.carrier := by
  by_contra h
  push Not at h
  obtain ⟨σ, hσ0, hσ1, hσ, hσU, hsave⟩ :=
    N.exists_core_excursion_replacement hepsilon hNU ht hγ hγU hcore h.1 h.2
  have hminσ : g.pathELength γ a b ≤ g.pathELength σ 0 1 := by
    rw [hmin]
    simpa only [hσ0, hσ1] using
      intrinsicEDist_le_pathELength g zero_le_one hσ hσU
  have hcancel : ENNReal.ofReal (N.end_neck.scale * N.epsilon⁻¹ / 8) ≤ 0 := by
    apply (ENNReal.add_le_add_iff_left hfinite).mp
    simpa only [add_zero] using
      (add_le_add hminσ (le_refl
        (ENNReal.ofReal (N.end_neck.scale * N.epsilon⁻¹ / 8)))).trans hsave
  have hpos : 0 < N.end_neck.scale * N.epsilon⁻¹ / 8 := by
    simpa only [N.end_neck_epsilon] using neck_shortening_saving_pos N.end_neck
  exact (not_le_of_gt (ENNReal.ofReal_pos.mpr hpos)) hcancel

end PoincareConjecture.CapCertificate
