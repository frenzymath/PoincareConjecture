import PoincareConjecture.Proofs.M32.Neck.NearbyTransport
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation.CollarDistance
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation.Diameter
















set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M32

section Scale

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}



private theorem sliceTransport_radius_lt_inv (N : EpsilonNeck g)
    (hsmall : N.epsilon ≤ 1 / (64 * Real.pi)) :
    32 * Real.pi < N.epsilon⁻¹ := by
  have hbound : 64 * Real.pi ≤ N.epsilon⁻¹ := by
    simpa only [one_div, inv_inv] using inv_anti₀ N.epsilon_pos hsmall
  linarith [Real.pi_pos]



private theorem sliceTransport_scale_le (N P : EpsilonNeck g)
    (hscalar : P.scale ^ 2 * P.connection.scalarCurvature N.center < 3 / 2) :
    P.scale ≤ 2 * N.scale := by
  have hnormal := neckScale_sq_mul_scalar_center_of_connection N P.connection
  have hmul := mul_lt_mul_of_pos_left hscalar (sq_pos_of_pos N.scale_pos)
  have hprod : N.scale ^ 2 * (P.scale ^ 2 * P.connection.scalarCurvature N.center) =
      P.scale ^ 2 := by
    calc
      _ = P.scale ^ 2 * (N.scale ^ 2 * P.connection.scalarCurvature N.center) := by ring
      _ = P.scale ^ 2 := by rw [hnormal, mul_one]
  rw [hprod] at hmul
  apply (sq_le_sq₀ P.scale_pos.le (mul_nonneg (by norm_num) N.scale_pos.le)).mp
  nlinarith [sq_nonneg N.scale]

end Scale

section SliceBounds

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M}



private theorem sliceTransport_slice_edist (N P : EpsilonNeck g)
    (hscale : P.scale ≤ 2 * N.scale) (hcenter : N.center ∈ P.carrier)
    (q : UnitTwoSphere) :
    g.edist N.center (P.coordinate_map (q, (P.coordinate_inverse N.center).2)) ≤
      ENNReal.ofReal ((4 * Real.pi) * N.scale) := by
  have ha := (P.coordinate_inverse_mem N.center hcenter).2
  have hmap : P.coordinate_map
      ((P.coordinate_inverse N.center).1, (P.coordinate_inverse N.center).2) =
      N.center := P.coordinate_map_coordinate_inverse hcenter
  have hdist := P.edist_coordinate_map_slice_le (P.coordinate_inverse N.center).1 q ha
  rw [hmap] at hdist
  apply hdist.trans
  apply ENNReal.ofReal_le_ofReal
  have hs : Real.sqrt (1 + P.epsilon) * Real.sqrt 2 ≤ 2 := by
    have hsq : (Real.sqrt (1 + P.epsilon) * Real.sqrt 2) ^ 2 =
        (1 + P.epsilon) * 2 := by
      rw [mul_pow, Real.sq_sqrt (by linarith [P.epsilon_pos]),
        Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    nlinarith [P.epsilon_lt_half, mul_nonneg (Real.sqrt_nonneg (1 + P.epsilon))
      (Real.sqrt_nonneg 2)]
  have hscaled := mul_le_mul_of_nonneg_left hs P.scale_pos.le
  have hpi := mul_le_mul_of_nonneg_right hscaled Real.pi_pos.le
  have hcompare := mul_le_mul_of_nonneg_left hscale
    (by positivity : 0 ≤ 2 * Real.pi)
  nlinarith



private theorem sliceTransport_slice_mem_closedCollar (N P : EpsilonNeck g)
    (hsmall : N.epsilon ≤ 1 / (64 * Real.pi))
    (hscale : P.scale ≤ 2 * N.scale) (hcenter : N.center ∈ P.carrier)
    (q : UnitTwoSphere) :
    P.coordinate_map (q, (P.coordinate_inverse N.center).2) ∈
      N.closedCollar (16 * Real.pi) := by
  have hr : 16 * Real.pi < N.epsilon⁻¹ := by
    linarith [sliceTransport_radius_lt_inv N hsmall, Real.pi_pos]
  by_contra hout
  have hlo := N.edist_center_lower_of_not_mem_closedCollar
    (by positivity : 0 < 16 * Real.pi) hr hout
  have hhi := sliceTransport_slice_edist N P hscale hcenter q
  have hbound := (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (by positivity) N.scale_pos.le)).mp (hlo.trans hhi)
  have hsqrt : (1 / 2 : ℝ) ≤ Real.sqrt (1 - N.epsilon) := by
    have hsq := Real.sq_sqrt (show 0 ≤ 1 - N.epsilon by
      linarith [N.epsilon_lt_half])
    nlinarith [Real.sqrt_nonneg (1 - N.epsilon), N.epsilon_lt_half]
  have hmul := mul_le_mul_of_nonneg_left hsqrt
    (mul_nonneg N.scale_pos.le (by positivity : 0 ≤ 16 * Real.pi))
  nlinarith [mul_pos Real.pi_pos N.scale_pos]

end SliceBounds





theorem exists_center_slice_graph_in_fixed_collar :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ 1 / 200 ∧
      epsilon₀ ≤ 1 / (64 * Real.pi) ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M} (N P : EpsilonNeck g),
        N.epsilon ≤ epsilon₀ → P.epsilon ≤ epsilon₀ → N.center ∈ P.carrier →
        ∃ h : UnitTwoSphere → ℝ, Continuous h ∧
          (∀ q, h q ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) ∧
          (∀ q, |h q| ≤ 16 * Real.pi) ∧
          range (fun q : UnitTwoSphere =>
            P.coordinate_map (q, (P.coordinate_inverse N.center).2)) =
            range (fun q => N.coordinate_map (q, h q)) := by
  obtain ⟨epsilon₁, hpos₁, _, hscalar⟩ :=
    exists_neck_scalarControl.{u} (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨epsilon₂, hpos₂, _, hricci⟩ := EpsilonNeck.exists_ricci_quadratic_control.{u}
  let epsilon₀ := min (min epsilon₁ epsilon₂) (min (1 / 200) (1 / (64 * Real.pi)))
  have hpos₀ : 0 < epsilon₀ :=
    lt_min (lt_min hpos₁ hpos₂) (lt_min (by norm_num) (by positivity))
  have he₁ : epsilon₀ ≤ epsilon₁ := (min_le_left _ _).trans (min_le_left _ _)
  have he₂ : epsilon₀ ≤ epsilon₂ := (min_le_left _ _).trans (min_le_right _ _)
  have hsmall : epsilon₀ ≤ 1 / 200 := (min_le_right _ _).trans (min_le_left _ _)
  have hfixed : epsilon₀ ≤ 1 / (64 * Real.pi) :=
    (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨epsilon₀, hpos₀, hsmall, hfixed, ?_⟩
  intro M _ _ _ _ _ _ _ g N P hN hP hcenter
  have hscalarP := hscalar P (hP.trans he₁) N.center hcenter
  have hscale : P.scale ≤ 2 * N.scale :=
    sliceTransport_scale_le N P (by linarith [(abs_lt.mp hscalarP).2])
  have hcollar := sliceTransport_slice_mem_closedCollar N P (hN.trans hfixed)
    hscale hcenter
  have hr : 16 * Real.pi < N.epsilon⁻¹ := by
    linarith [sliceTransport_radius_lt_inv N (hN.trans hfixed), Real.pi_pos]
  have hmem (q : UnitTwoSphere) :
      P.coordinate_map (q, (P.coordinate_inverse N.center).2) ∈ N.carrier :=
    N.closedCollar_subset_carrier hr (hcollar q)
  have ha := (P.coordinate_inverse_mem N.center hcenter).2
  have hbij (q : UnitTwoSphere) :=
    N.sphereSlice_projection_mfderiv_bijective_of_ricci_error P.connection P ha q
      (hmem q) hscale (hricci N P.connection (hN.trans he₂))
      (hricci P P.connection (hP.trans he₂))
  have hprojection : IsLocalHomeomorph (fun q : UnitTwoSphere =>
      (N.coordinate_inverse (P.coordinate_map (q, (P.coordinate_inverse N.center).2))).1) := by
    apply IsLocalDiffeomorph.isLocalHomeomorph (I := 𝓡 2) (J := 𝓡 2) (n := ∞)
    apply Poincare.isLocalDiffeomorph_of_contMDiff_bijective_mfderiv (hbij := hbij)
    have hc : ContMDiff (𝓡 2) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
        (fun q : UnitTwoSphere =>
          N.coordinate_inverse (P.coordinate_map (q, (P.coordinate_inverse N.center).2))) := by
      intro q
      exact (N.coordinate_inverse_smooth.contMDiffAt
        (N.carrier_open.mem_nhds (hmem q))).comp q (P.sphereSlice_contMDiff ha q)
    exact contMDiff_fst.comp hc
  obtain ⟨h, hh, hdom, hrange⟩ := N.exists_continuous_graph_of_isLocalHomeomorph
    (fun q : UnitTwoSphere => P.coordinate_map (q, (P.coordinate_inverse N.center).2))
    (P.sphereSlice_contMDiff ha).continuous hmem hprojection
  refine ⟨h, hh, hdom, ?_, hrange⟩
  intro q
  have hpoint : N.coordinate_map (q, h q) ∈ N.closedCollar (16 * Real.pi) := by
    have hpoint' : N.coordinate_map (q, h q) ∈ range (fun p : UnitTwoSphere =>
        P.coordinate_map (p, (P.coordinate_inverse N.center).2)) := by
      rw [hrange]
      exact mem_range_self q
    obtain ⟨p, hp⟩ := hpoint'
    rw [← hp]
    exact hcollar p
  obtain ⟨⟨p, t⟩, ⟨_, ht⟩, heq⟩ := hpoint
  have htN : (p, t) ∈ N.cylinderDomain :=
    ⟨mem_univ _, by constructor <;> linarith [ht.1, ht.2]⟩
  have hinverse := congrArg N.coordinate_inverse heq
  rw [N.coordinate_inverse_coordinate_map htN,
    N.coordinate_inverse_coordinate_map ⟨mem_univ _, hdom q⟩] at hinverse
  have hheight : t = h q := congrArg Prod.snd hinverse
  exact abs_le.mpr ⟨by simpa only [hheight] using ht.1,
    by simpa only [hheight] using ht.2⟩





theorem exists_center_in_carrier_compact_transport :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ 1 / 200 ∧
      epsilon₀ ≤ 1 / (64 * Real.pi) ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M} (N P : EpsilonNeck g),
        N.epsilon ≤ epsilon₀ → P.epsilon ≤ epsilon₀ → N.center ∈ P.carrier →
        ∃ (e : M ≃ₜ M) (K : Set M), IsCompact K ∧
          K ⊆ N.closedCollar (32 * Real.pi) ∪ P.carrier ∧
          (∀ x, x ∉ K → e x = x) ∧ e '' N.central_sphere = P.central_sphere := by
  obtain ⟨epsilon₀, hpos, hsmall, hfixed, hgraph⟩ :=
    exists_center_slice_graph_in_fixed_collar.{u}
  refine ⟨epsilon₀, hpos, hsmall, hfixed, ?_⟩
  intro M _ _ _ _ _ _ _ g N P hN hP hcenter
  obtain ⟨h, hh, _, hheight, hslice⟩ := hgraph N P hN hP hcenter
  have hr : 0 < 32 * Real.pi := by positivity
  have hrN : 32 * Real.pi < N.epsilon⁻¹ :=
    sliceTransport_radius_lt_inv N (hN.trans hfixed)
  have hbound (q : UnitTwoSphere) : |h q| < 32 * Real.pi := by
    linarith [hheight q, Real.pi_pos]
  have ha := (P.coordinate_inverse_mem N.center hcenter).2
  obtain ⟨s, hs, hsP, habound⟩ :=
    P.exists_graph_collar (fun _ => (P.coordinate_inverse N.center).2)
      continuous_const (fun _ => ha)
  let eN := N.graphTransport hr hrN h hh hbound
  let eP := P.graphTransport hs hsP
    (fun _ => (P.coordinate_inverse N.center).2) continuous_const habound
  have hNsphere : eN '' N.central_sphere = range (fun q : UnitTwoSphere =>
      P.coordinate_map (q, (P.coordinate_inverse N.center).2)) :=
    (N.graphTransport_image_central_sphere hr hrN h hh hbound).trans hslice.symm
  have hPsphere : eP '' P.central_sphere = range (fun q : UnitTwoSphere =>
      P.coordinate_map (q, (P.coordinate_inverse N.center).2)) :=
    P.graphTransport_image_central_sphere hs hsP
      (fun _ => (P.coordinate_inverse N.center).2) continuous_const habound
  refine ⟨eN.trans eP.symm, N.closedCollar (32 * Real.pi) ∪ P.closedCollar s,
    (N.isCompact_closedCollar hrN).union (P.isCompact_closedCollar hsP),
    union_subset_union subset_rfl (P.closedCollar_subset_carrier hsP), ?_, ?_⟩
  · intro x hx
    have hxN : x ∉ N.closedCollar (32 * Real.pi) := fun h => hx (Or.inl h)
    have hxP : x ∉ P.closedCollar s := fun h => hx (Or.inr h)
    have hfixN : eN x = x := N.graphTransport_fixed hr hrN h hh hbound hxN
    have hfixP : eP x = x := P.graphTransport_fixed hs hsP
      (fun _ => (P.coordinate_inverse N.center).2) continuous_const habound hxP
    change eP.symm (eN x) = x
    rw [hfixN]
    exact eP.symm_apply_eq.mpr hfixP.symm
  · change (eP.symm ∘ eN) '' N.central_sphere = P.central_sphere
    rw [image_comp, hNsphere, ← hPsphere]
    exact eP.toEquiv.symm_image_image _

end PoincareConjecture.M32
