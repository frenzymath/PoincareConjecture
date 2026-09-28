import PoincareConjecture.Proofs.M28.Sec10_3_Tube.NeckSpherePaths
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.IntrinsicOpenMetric
import Mathlib.Data.Finset.Card










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28




theorem exists_standardSphere_small_path_cover {tau : ℝ} (htau : 0 < tau) :
    ∃ F : Finset UnitTwoSphere, ∀ q : UnitTwoSphere, ∃ z ∈ F,
      ∃ gamma : ℝ → UnitTwoSphere, gamma 0 = q ∧ gamma 1 = z ∧
        ContMDiff 𝓘(ℝ, ℝ) (𝓡 2) 1 gamma ∧
        standardSphereMetric.pathELength gamma 0 1 < ENNReal.ofReal tau := by
  classical
  have hs : IsConnected (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    isConnected_sphere (by rw [← Module.finrank_eq_rank]; norm_num) _ (by norm_num)
  let : ConnectedSpace UnitTwoSphere := Subtype.connectedSpace hs
  let : Bundle.RiemannianBundle
      (TangentSpace (𝓡 2) : UnitTwoSphere → Type _) :=
    ⟨standardSphereMetric.toRiemannianMetric⟩
  let O : UnitTwoSphere → Set UnitTwoSphere :=
    fun z => {q | (standardSphereMetric.edist z q).toReal < tau}
  have hopen (z : UnitTwoSphere) : IsOpen (O z) :=
    isOpen_lt (standardSphereMetric.continuous_toReal_edist z) continuous_const
  have hcover : (univ : Set UnitTwoSphere) ⊆ ⋃ z, O z := by
    intro q _hq
    refine mem_iUnion.mpr ⟨q, ?_⟩
    change (standardSphereMetric.edist q q).toReal < tau
    have hzero : standardSphereMetric.edist q q = 0 := Manifold.riemannianEDist_self
    simpa only [hzero, ENNReal.toReal_zero] using htau
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover O hopen hcover
  refine ⟨F, ?_⟩
  intro q
  obtain ⟨z, hzF, hq⟩ := mem_iUnion₂.mp (hF (mem_univ q))
  have hdist : standardSphereMetric.edist q z < ENNReal.ofReal tau := by
    apply (ENNReal.toReal_lt_toReal (standardSphereMetric.edist_ne_top q z)
      ENNReal.ofReal_ne_top).mp
    rw [ENNReal.toReal_ofReal htau.le]
    have hcomm : standardSphereMetric.edist q z = standardSphereMetric.edist z q :=
      Manifold.riemannianEDist_comm
    rw [hcomm]
    exact hq
  obtain ⟨gamma, h0, h1, hgamma, hlength, _hflat0, _hflat1⟩ :=
    Manifold.exists_lt_locally_constant_of_riemannianEDist_lt hdist zero_lt_one
  exact ⟨z, hzF, gamma, h0, h1, hgamma, hlength⟩

private theorem intrinsicEDist_coordinate_sphere_path_lt
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} (N : EpsilonNeck g)
    {V : Set M} (hSV : N.central_sphere ⊆ V)
    {p q : UnitTwoSphere} {tau : ℝ}
    {gamma : ℝ → UnitTwoSphere} (h0 : gamma 0 = p) (h1 : gamma 1 = q)
    (hgamma : ContMDiff 𝓘(ℝ, ℝ) (𝓡 2) 1 gamma)
    (hlength : standardSphereMetric.pathELength gamma 0 1 < ENNReal.ofReal tau) :
    intrinsicEDist g V (N.coordinate_map (p, 0)) (N.coordinate_map (q, 0)) <
      ENNReal.ofReal (4 * N.scale * tau) := by
  have hzero : (0 : ℝ) ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
    ⟨neg_neg_of_pos (inv_pos.mpr N.epsilon_pos), inv_pos.mpr N.epsilon_pos⟩
  let sigma : ℝ → M := fun t => N.coordinate_map (gamma t, 0)
  have hsmooth : ContMDiff 𝓘(ℝ, ℝ) (𝓡 3) 1 sigma := by
    rw [← contMDiffOn_univ]
    apply (N.coordinate_map_smooth.of_le (by simp)).comp
    · exact (hgamma.prodMk contMDiff_const).contMDiffOn
    · intro t _ht
      exact ⟨mem_univ _, hzero⟩
  have hmap : MapsTo sigma (Icc (0 : ℝ) 1) V := by
    intro t _ht
    apply hSV
    rw [N.central_sphere_eq]
    exact ⟨(gamma t, 0), ⟨mem_univ _, rfl⟩, rfl⟩
  have hle := intrinsicEDist_le_pathELength g zero_le_one hsmooth.contMDiffOn hmap
  have hscale : 0 < 4 * N.scale := mul_pos (by norm_num) N.scale_pos
  have hbound := (coordinate_sphere_pathELength_le N hgamma hzero 0 1).trans_lt
    (ENNReal.mul_lt_mul_right (ne_of_gt (ENNReal.ofReal_pos.mpr hscale))
      ENNReal.ofReal_ne_top hlength)
  have hbound' : g.pathELength sigma 0 1 < ENNReal.ofReal (4 * N.scale * tau) := by
    simpa only [sigma, ← ENNReal.ofReal_mul hscale.le] using hbound
  have hfinal := hle.trans_lt hbound'
  simpa only [sigma, h0, h1] using hfinal





theorem exists_central_sphere_packing_number {eta : ℝ} (heta : 0 < eta) :
    ∃ K : ℕ, 1 ≤ K ∧
      ∀ (M : Type u) [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        (g : RiemannianMetric 3 M) (N : EpsilonNeck g)
        (U : TopologicalSpace.Opens M), N.central_sphere ⊆ (U : Set M) →
        ∀ x : Fin (K + 1) → U, (∀ j, (x j : M) ∈ N.central_sphere) →
          ∃ i j : Fin (K + 1), i ≠ j ∧
            (intrinsicOpenMetric g U).edist (x i) (x j) <
              ENNReal.ofReal (eta * N.scale) := by
  classical
  let tau : ℝ := eta / 16
  have htau : 0 < tau := div_pos heta (by norm_num)
  obtain ⟨F, hcover⟩ := exists_standardSphere_small_path_cover htau
  let K : ℕ := F.card + 1
  refine ⟨K, by dsimp only [K]; omega, ?_⟩
  intro M _ _ _ g N U hSU x hx
  let gU := intrinsicOpenMetric g U
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : U → Type _) :=
    ⟨gU.toRiemannianMetric⟩
  have hcoords (j : Fin (K + 1)) :
      ∃ q : UnitTwoSphere, N.coordinate_map (q, 0) = (x j : M) := by
    have h := hx j
    rw [N.central_sphere_eq] at h
    obtain ⟨⟨q, s⟩, ⟨_hq, hs⟩, hq⟩ := h
    have hs0 : s = 0 := hs
    subst s
    exact ⟨q, hq⟩
  choose q hq using hcoords
  choose z hz gamma h0 h1 hgamma hlength using fun j => hcover (q j)
  have hcard : F.card < (Finset.univ : Finset (Fin (K + 1))).card := by
    simp only [Finset.card_univ, Fintype.card_fin, K]
    omega
  obtain ⟨i, _hi, j, _hj, hij, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to (f := z) hcard
      (fun j (_hj : j ∈ (Finset.univ : Finset (Fin (K + 1)))) => hz j)
  have hzS : N.coordinate_map (z i, 0) ∈ N.central_sphere := by
    rw [N.central_sphere_eq]
    exact ⟨(z i, 0), ⟨mem_univ _, rfl⟩, rfl⟩
  let center : U := ⟨N.coordinate_map (z i, 0), hSU hzS⟩
  let B : ℝ := 4 * N.scale * tau
  have hB : 0 ≤ B := (mul_pos (mul_pos (by norm_num) N.scale_pos) htau).le
  have hleft : gU.edist (x i) center < ENNReal.ofReal B := by
    rw [intrinsicOpenMetric_edist]
    change intrinsicEDist g (U : Set M) (x i : M) (N.coordinate_map (z i, 0)) < _
    rw [← hq i]
    exact intrinsicEDist_coordinate_sphere_path_lt N hSU
      (h0 i) (h1 i) (hgamma i) (hlength i)
  have hright : gU.edist (x j) center < ENNReal.ofReal B := by
    rw [intrinsicOpenMetric_edist]
    change intrinsicEDist g (U : Set M) (x j : M) (N.coordinate_map (z i, 0)) < _
    rw [← hq j, heq]
    exact intrinsicEDist_coordinate_sphere_path_lt N hSU
      (h0 j) (h1 j) (hgamma j) (hlength j)
  have htriangle : gU.edist (x i) (x j) ≤
      gU.edist (x i) center + gU.edist (x j) center := by
    have hcomm : gU.edist center (x j) = gU.edist (x j) center :=
      Manifold.riemannianEDist_comm
    simpa only [hcomm] using
      (show gU.edist (x i) (x j) ≤ gU.edist (x i) center + gU.edist center (x j) from
        Manifold.riemannianEDist_triangle)
  refine ⟨i, j, hij, ?_⟩
  have hsum := htriangle.trans_lt (ENNReal.add_lt_add hleft hright)
  rw [← ENNReal.ofReal_add hB hB] at hsum
  apply hsum.trans_le
  apply ENNReal.ofReal_le_ofReal
  have hpos : 0 < eta * N.scale := mul_pos heta N.scale_pos
  dsimp only [B, tau]
  nlinarith only [hpos]

end PoincareConjecture.M28
