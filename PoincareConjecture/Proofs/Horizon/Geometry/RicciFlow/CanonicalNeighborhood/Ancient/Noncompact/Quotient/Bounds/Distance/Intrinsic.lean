import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Quotient.Bounds.Distance
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Quotient.StrongNeck
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Quotient.CoreTopology
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geodesic.Intrinsic
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geodesic.Calibration

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Poincare.Geometry.Riemannian.SpaceForm
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M27TwistedSphereLineFlowCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M}

private theorem cylinder_slab_intrinsicEDist_le {r : ℝ}
    (z w : RoundCylinderSpace) (hz : z.2 ∈ Ioo (-r) r) (hw : w.2 ∈ Ioo (-r) r) :
    letI := RiemannianMetric.lineProductChartedSpace (n := 2) (M := UnitTwoSphere)
    letI := RiemannianMetric.lineProductIsManifold (n := 2) (M := UnitTwoSphere)
    intrinsicEDist roundCylinderMetric (univ ×ˢ Ioo (-r) r) z w ≤
      ENNReal.ofReal (Real.sqrt 2 * (Real.pi + 1) + |z.2 - w.2|) := by
  let := RiemannianMetric.lineProductChartedSpace (n := 2) (M := UnitTwoSphere)
  let := RiemannianMetric.lineProductIsManifold (n := 2) (M := UnitTwoSphere)
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : UnitTwoSphere → Type _) :=
    ⟨(roundSphereMetric 2).toRiemannianMetric⟩
  have hd : (roundSphereMetric 2).edist z.1 w.1 < ENNReal.ofReal (Real.pi + 1) := by
    rw [roundSphereMetric_edist_eq_angle (by norm_num : 1 ≤ 2)]
    apply (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
    exact (Real.arccos_le_pi _).trans_lt (by linarith)
  obtain ⟨σ, h0, h1, hσ, hlen⟩ := Manifold.exists_lt_of_riemannianEDist_lt hd
  let η : ℝ → RoundCylinderSpace := fun s => (σ s, z.2 + s * (w.2 - z.2))
  let e := roundCylinderModelDiffeomorph
  have hη := EpsilonNeck.model_path_smooth (z := z) (w := w) hσ
  have hpath : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 (e ∘ η) (Icc (0 : ℝ) 1) :=
    (e.contMDiff.of_le (by simp : (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω))).comp_contMDiffOn hη
  apply roundCylinderMetric.intrinsicEDist_le_of_path hpath
    (by change (σ 0, z.2 + 0 * (w.2 - z.2)) = z; simp [h0])
    (by change (σ 1, z.2 + 1 * (w.2 - z.2)) = w; simp [h1])
  · apply image_subset_iff.mpr
    intro s hs
    refine ⟨mem_univ _, ?_⟩
    change z.2 + s * (w.2 - z.2) ∈ Ioo (-r) r
    apply (convex_Ioo (𝕜 := ℝ) (-r) r).segment_subset hz hw
    rw [segment_eq_image' (𝕜 := ℝ) z.2 w.2]
    exact ⟨s, hs, rfl⟩
  · have h := EpsilonNeck.model_path_length_le (z := z) (w := w) hσ hlen.le
    rwa [ENNReal.ofReal_add (by positivity) (abs_nonneg _)]

private theorem normalizedCover_tangentNorm
    (C : M27TwistedSphereLineFlowCertificate K) {t : ℝ} (ht : t ≤ 0)
    (p : UnitTwoSphere × ℝ)
    (hR : 0 < (K.flow.connection t).scalarCurvature (C.cover p))
    (a : UnitTwoSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ UnitTwoSphere)
    (ha : ∀ (x : UnitTwoSphere) (v w : TangentSpace (𝓡 2) x),
      (K.flow.connection t).scalarCurvature (C.cover p) *
        (C.sphere.metric t).inner (a x)
          (mfderiv (𝓡 2) (𝓡 2) a x v) (mfderiv (𝓡 2) (𝓡 2) a x w) =
            2 * (roundSphereMetric 2).inner x v w) :
    letI := RiemannianMetric.lineProductChartedSpace (n := 2) (M := UnitTwoSphere)
    letI := RiemannianMetric.lineProductIsManifold (n := 2) (M := UnitTwoSphere)
    let F := C.normalizedCover a ((K.flow.connection t).scalarCurvature (C.cover p)) p.2 hR ∘
      roundCylinderModelDiffeomorph.symm
    ∀ z v, (K.flow.metric t).tangentNorm (F z) (mfderiv (𝓡 3) (𝓡 3) F z v) =
      (Real.sqrt ((K.flow.connection t).scalarCurvature (C.cover p)))⁻¹ *
        roundCylinderMetric.tangentNorm z v := by
  let := RiemannianMetric.lineProductChartedSpace (n := 2) (M := UnitTwoSphere)
  let := RiemannianMetric.lineProductIsManifold (n := 2) (M := UnitTwoSphere)
  let R := (K.flow.connection t).scalarCurvature (C.cover p)
  let Φ := C.normalizedCover a R p.2 hR
  let e := roundCylinderModelDiffeomorph
  let F := Φ ∘ e.symm
  have hF : ContMDiff (𝓡 3) (𝓡 3) ∞ F :=
    (C.normalizedCover_localDiffeomorph a R p.2 hR).contMDiff.comp e.symm.contMDiff
  have hcomp : F ∘ e = Φ := by ext z; simp [F]
  change ∀ (z : RoundCylinderSpace) (v : TangentSpace (𝓡 3) z),
    (K.flow.metric t).tangentNorm (F z) (mfderiv (𝓡 3) (𝓡 3) F z v) =
      (Real.sqrt R)⁻¹ * roundCylinderMetric.tangentNorm z v
  intro z v
  obtain ⟨x, rfl⟩ := e.surjective z
  obtain ⟨w, rfl⟩ := (e.mfderivToContinuousLinearEquiv (by simp) x).surjective v
  have hd : mfderiv (𝓡 3) (𝓡 3) F (e x)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e x w) =
      mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) Φ x w := by
    rw [← mfderiv_comp_apply x (hF.mdifferentiable (by simp) _)
      (e.mdifferentiable (by simp) _), hcomp]
  have hm := congrFun (congrFun (congrFun
    (C.normalizedCover_metric ht p hR a ha (u := 0) le_rfl) x) w) w
  simp only [zero_div, add_zero] at hm
  have hm' : (K.flow.metric t).inner (Φ x)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) Φ x w)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) Φ x w) =
      R⁻¹ * EvolvingRoundCylinderMetric 0 x w w := by
    change R * _ = _ at hm
    rw [← hm, inv_mul_cancel_left₀ hR.ne']
    rfl
  change Real.sqrt ((K.flow.metric t).inner (F (e x))
    (mfderiv (𝓡 3) (𝓡 3) F (e x) (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e x w))
    (mfderiv (𝓡 3) (𝓡 3) F (e x) (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e x w))) =
      (Real.sqrt R)⁻¹ * Real.sqrt (roundCylinderMetric.inner (e x)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e x w)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e x w))
  rw [hd, show F (e x) = Φ x from congrFun hcomp x, hm', Real.sqrt_mul (inv_nonneg.mpr hR.le),
    Real.sqrt_inv]
  change (Real.sqrt R)⁻¹ * Real.sqrt _ = (Real.sqrt R)⁻¹ * Real.sqrt _
  rw [roundCylinderMetric_inner]

private theorem normalizedCover_slab_intrinsicEDist_le
    (C : M27TwistedSphereLineFlowCertificate K) {t : ℝ} (ht : t ≤ 0)
    (p : UnitTwoSphere × ℝ)
    (hR : 0 < (K.flow.connection t).scalarCurvature (C.cover p))
    (a : UnitTwoSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ UnitTwoSphere)
    (ha : ∀ (x : UnitTwoSphere) (v w : TangentSpace (𝓡 2) x),
      (K.flow.connection t).scalarCurvature (C.cover p) *
        (C.sphere.metric t).inner (a x)
          (mfderiv (𝓡 2) (𝓡 2) a x v) (mfderiv (𝓡 2) (𝓡 2) a x w) =
            2 * (roundSphereMetric 2).inner x v w)
    {r : ℝ} (z w : RoundCylinderSpace) (hz : z.2 ∈ Ioo (-r) r) (hw : w.2 ∈ Ioo (-r) r) :
    let R := (K.flow.connection t).scalarCurvature (C.cover p)
    let Φ := C.normalizedCover a R p.2 hR
    intrinsicEDist (K.flow.metric t) (Φ '' (univ ×ˢ Ioo (-r) r)) (Φ z) (Φ w) ≤
      ENNReal.ofReal ((Real.sqrt 2 * (Real.pi + 1) + |z.2 - w.2|) / Real.sqrt R) := by
  let := RiemannianMetric.lineProductChartedSpace (n := 2) (M := UnitTwoSphere)
  let := RiemannianMetric.lineProductIsManifold (n := 2) (M := UnitTwoSphere)
  let R := (K.flow.connection t).scalarCurvature (C.cover p)
  let Φ := C.normalizedCover a R p.2 hR
  let F := Φ ∘ roundCylinderModelDiffeomorph.symm
  have hF : ContMDiff (𝓡 3) (𝓡 3) 1 F :=
    ((C.normalizedCover_localDiffeomorph a R p.2 hR).contMDiff.comp
      roundCylinderModelDiffeomorph.symm.contMDiff).of_le (by simp)
  have hbound := C.normalizedCover_tangentNorm ht p hR a ha
  have h := roundCylinderMetric.intrinsicEDist_image_le_of_tangentNorm_le
    (K.flow.metric t) (isOpen_univ.prod isOpen_Ioo) hF.contMDiffOn
    (V := Φ '' (univ ×ˢ Ioo (-r) r))
    (fun x hx => show Φ x ∈ Φ '' (univ ×ˢ Ioo (-r) r) from mem_image_of_mem Φ hx)
    (inv_pos.mpr (Real.sqrt_pos.mpr hR)) (fun x _ v => (hbound x v).le) z w
  apply (h.trans (mul_le_mul_of_nonneg_left (cylinder_slab_intrinsicEDist_le z w hz hw)
    zero_le)).trans_eq
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr (Real.sqrt_nonneg R))]
  congr 1
  rw [div_eq_mul_inv, mul_comm]

theorem intrinsicEDist_interior_slabCore_le
    (C : M27TwistedSphereLineFlowCertificate K) {t : ℝ} (ht : t ≤ 0)
    (q : UnitTwoSphere) {r : ℝ} {x y : M}
    (hx : x ∈ interior (C.slabCore r)) (hy : y ∈ interior (C.slabCore r)) :
    intrinsicEDist (K.flow.metric t) (interior (C.slabCore r)) x y ≤
      ENNReal.ofReal (2 * r + Real.sqrt 2 * (Real.pi + 1) /
        Real.sqrt ((K.flow.connection t).scalarCurvature (C.cover (q, 0)))) := by
  obtain ⟨hR, a, ha⟩ := C.exists_scalarNormalized_sphere ht (q, 0)
  let R := (K.flow.connection t).scalarCurvature (C.cover (q, 0))
  have hsqrt : 0 < Real.sqrt R := Real.sqrt_pos.mpr hR
  let u := r * Real.sqrt R
  let Φ := C.normalizedCover a R 0 hR
  have him : Φ '' (univ ×ˢ Ioo (-u) u) = interior (C.slabCore r) := by
    rw [C.interior_slabCore]
    change C.normalizedCover a R 0 hR '' _ = _
    rw [C.normalizedCover_image_interval]
    simp [u, neg_div, hsqrt.ne']
  obtain ⟨z, hz, rfl⟩ := him ▸ hx
  obtain ⟨w, hw, rfl⟩ := him ▸ hy
  have h := C.normalizedCover_slab_intrinsicEDist_le ht (q, 0) hR a ha z w hz.2 hw.2
  change intrinsicEDist (K.flow.metric t) (Φ '' _) (Φ z) (Φ w) ≤ _ at h
  rw [him] at h
  apply h.trans (ENNReal.ofReal_le_ofReal ?_)
  have hline : |z.2 - w.2| ≤ 2 * u := by
    rw [abs_le]
    constructor <;> linarith [hz.2.1, hz.2.2, hw.2.1, hw.2.2]
  calc
    (Real.sqrt 2 * (Real.pi + 1) + |z.2 - w.2|) / Real.sqrt R ≤
        (Real.sqrt 2 * (Real.pi + 1) + 2 * u) / Real.sqrt R :=
      div_le_div_of_nonneg_right (add_le_add le_rfl hline) hsqrt.le
    _ = 2 * r + Real.sqrt 2 * (Real.pi + 1) / Real.sqrt R := by
      dsimp [u]
      field_simp
      ring

theorem intrinsicDiameter_interior_slabCore_le
    (C : M27TwistedSphereLineFlowCertificate K) {t : ℝ} (ht : t ≤ 0)
    (q : UnitTwoSphere) (r : ℝ) :
    intrinsicDiameter (K.flow.metric t) (interior (C.slabCore r)) ≤
      ENNReal.ofReal (2 * r + Real.sqrt 2 * (Real.pi + 1) /
        Real.sqrt ((K.flow.connection t).scalarCurvature (C.cover (q, 0)))) := by
  apply sSup_le
  rintro _ ⟨⟨x, y⟩, rfl⟩
  exact C.intrinsicEDist_interior_slabCore_le ht q x.property y.property

theorem interior_slabCore_subset_ball
    (C : M27TwistedSphereLineFlowCertificate K) {t : ℝ} (ht : t ≤ 0)
    (q : UnitTwoSphere) {r B : ℝ} (hr : 0 < r)
    (hB : 2 * r + Real.sqrt 2 * (Real.pi + 1) /
      Real.sqrt ((K.flow.connection t).scalarCurvature (C.cover (q, 0))) < B) :
    interior (C.slabCore r) ⊆ (K.flow.metric t).ball (C.cover (q, 0)) B := by
  intro x hx
  have hq : C.cover (q, 0) ∈ interior (C.slabCore r) := by
    rw [C.cover_mem_interior_slabCore_iff]
    simpa only [abs_zero] using hr
  have h := ((K.flow.metric t).edist_le_intrinsicEDist _ _ _).trans
    (C.intrinsicEDist_interior_slabCore_le ht q hq hx)
  have hBpos : 0 < B := by
    have hnonneg : 0 ≤ Real.sqrt 2 * (Real.pi + 1) /
        Real.sqrt ((K.flow.connection t).scalarCurvature (C.cover (q, 0))) := by positivity
    linarith
  exact h.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hBpos).mpr hB)

theorem closure_ball_subset_slabCore
    (C : M27TwistedSphereLineFlowCertificate K) {t r R : ℝ} (ht : t ≤ 0) (hR : 0 ≤ R)
    {x : M} (hx : x ∈ C.slabCore r) :
    closure ((K.flow.metric t).ball x R) ⊆ C.slabCore (r + R) := by
  apply closure_minimal _ (C.isCompact_slabCore (r + R)).isClosed
  intro y hy
  exact C.edist_le_mem_slabCore ht hR hx hy.le

theorem closure_ball_subset_interior_slabCore
    (C : M27TwistedSphereLineFlowCertificate K) {t r R s : ℝ} (ht : t ≤ 0) (hR : 0 ≤ R)
    {x : M} (hx : x ∈ C.slabCore r) (hrs : r + R < s) :
    closure ((K.flow.metric t).ball x R) ⊆ interior (C.slabCore s) := by
  intro y hy
  have hmem := C.closure_ball_subset_slabCore ht hR hx hy
  obtain ⟨p, rfl⟩ := C.cover_surjective y
  rw [C.cover_mem_slabCore_iff] at hmem
  exact (C.cover_mem_interior_slabCore_iff s p).mpr (hmem.trans_lt hrs)

end PoincareConjecture.M27TwistedSphereLineFlowCertificate
