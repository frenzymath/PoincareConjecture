import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.Core.Affine.Model
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Neck.Static.Constructor
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Neck.Spatial
import Mathlib.Geometry.Manifold.Algebra.Structures



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

noncomputable section

namespace PoincareConjecture.RoundCylinderAffine

def inverseSpace (a s : ℝ) (z : RoundCylinderSpace) : RoundCylinderSpace :=
  (z.1, (z.2 - s) / a)

theorem inverseSpace_space {a : ℝ} (ha : a ≠ 0) (s : ℝ) (z : RoundCylinderSpace) :
    inverseSpace a s (space a s z) = z := by
  ext <;> simp [inverseSpace, space, ha]

theorem space_inverseSpace {a : ℝ} (ha : a ≠ 0) (s : ℝ) (z : RoundCylinderSpace) :
    space a s (inverseSpace a s z) = z := by
  apply Prod.ext
  · rfl
  · dsimp [inverseSpace, space]
    field_simp
    ring

theorem contMDiff_space (a s : ℝ) :
    ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ (space a s) :=
  contMDiff_fst.prodMk ((contMDiff_const.mul contMDiff_snd).add contMDiff_const)

theorem contMDiff_inverseSpace (a s : ℝ) :
    ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ (inverseSpace a s) :=
  contMDiff_fst.prodMk ((contMDiff_snd.sub contMDiff_const).div_const a)


theorem metric_pullback_affine
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M) (f : RoundCylinderSpace → M)
    (a s : ℝ) (z : RoundCylinderSpace)
    (hf : MDifferentiableAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) f (space a s z))
    (v w : RoundCylinderTangent z) :
    roundCylinderPullback g (f ∘ space a s) z v w =
      pullback a s (roundCylinderPullback g f) z v w := by
  have hs := ((contMDiff_space a s) z).mdifferentiableAt (by simp)
  have hder (v : RoundCylinderTangent z) :
      mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) (space a s) z v =
        (v.1, a * v.2) := by
    have hh := CylinderGluing.mfderiv_axial_map_apply z
      (((hasDerivAt_id z.2).const_mul a).add_const s) v
    dsimp only [TangentSpace] at hh ⊢
    change mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ))
      (fun p : RoundCylinderSpace => (p.1, a * p.2 + s)) z v = (v.1, a * v.2)
    simpa only [TangentSpace, id_eq, mul_one] using hh
  unfold roundCylinderPullback pullback
  rw [mfderiv_comp z hf hs]
  dsimp only [TangentSpace]
  change g.inner (f (space a s z))
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) f (space a s z)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) (space a s) z v))
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) f (space a s z)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) (space a s) z w)) = _
  rw [hder, hder]
  rfl

end PoincareConjecture.RoundCylinderAffine

namespace PoincareConjecture.EpsilonNeck

open RoundCylinderAffine

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} (N : EpsilonNeck g)
  {δ a : ℝ} (ha : 0 < a) (s : ℝ)
  (hsub : MapsTo (fun z : ℝ => a * z + s)
    (Ioo (-δ⁻¹) δ⁻¹) (Ioo (-N.epsilon⁻¹) N.epsilon⁻¹))

def affineCoordinate : OpenPartialHomeomorph RoundCylinderSpace M where
  toFun := N.coordinate_map ∘ space a s
  invFun := inverseSpace a s ∘ N.coordinate_inverse
  source := univ ×ˢ Ioo (-δ⁻¹) δ⁻¹
  target := N.region (a * (-δ⁻¹) + s) (a * δ⁻¹ + s)
  map_source' := fun z hz => by
    have hzN : space a s z ∈ N.cylinderDomain := ⟨mem_univ _, hsub hz.2⟩
    refine ⟨N.coordinate_map_mem hzN, ?_⟩
    dsimp only [Function.comp_apply]
    rw [N.coordinate_inverse_coordinate_map hzN]
    simpa only [space, add_comm] using
      And.intro (add_lt_add_right (mul_lt_mul_of_pos_left hz.2.1 ha) s)
        (add_lt_add_right (mul_lt_mul_of_pos_left hz.2.2 ha) s)
  map_target' := fun x hx => by
    refine ⟨mem_univ _, ?_, ?_⟩
    · change -δ⁻¹ < ((N.coordinate_inverse x).2 - s) / a
      apply (lt_div_iff₀ ha).mpr
      nlinarith [hx.2.1]
    · change ((N.coordinate_inverse x).2 - s) / a < δ⁻¹
      apply (div_lt_iff₀ ha).mpr
      nlinarith [hx.2.2]
  left_inv' := fun z hz => by
    change inverseSpace a s (N.coordinate_inverse (N.coordinate_map (space a s z))) = z
    rw [N.coordinate_inverse_coordinate_map ⟨mem_univ _, hsub hz.2⟩,
      inverseSpace_space ha.ne']
  right_inv' := fun x hx => by
    change N.coordinate_map (space a s (inverseSpace a s (N.coordinate_inverse x))) = x
    rw [space_inverseSpace ha.ne', N.coordinate_map_coordinate_inverse hx.1]
  open_source := isOpen_univ.prod isOpen_Ioo
  open_target := N.coordinate_inverse_smooth.continuousOn.snd.isOpen_inter_preimage
    N.carrier_open isOpen_Ioo
  continuousOn_toFun :=
    (N.coordinate_map_smooth.comp (contMDiff_space a s).contMDiffOn
      (fun _ hz => ⟨mem_univ _, hsub hz.2⟩)).continuousOn
  continuousOn_invFun :=
    ((contMDiff_inverseSpace a s).comp_contMDiffOn
      (N.coordinate_inverse_smooth.mono (fun _ hx => hx.1))).continuousOn

include hsub in

theorem affine_pullback_close (h : RiemannianMetric 3 M) (R : ℝ)
    (hclose : RoundCylinderClose δ 0 (fun z v w =>
      R * pullback a s (roundCylinderPullback h N.coordinate_map) z v w)) :
    RoundCylinderClose δ 0 (fun z v w =>
      R * roundCylinderPullback h (N.coordinate_map ∘ space a s) z v w) := by
  apply DeepHorn.roundCylinderClose_congr_axial (B := fun z v w =>
    R * pullback a s (roundCylinderPullback h N.coordinate_map) z v w) _ hclose
  intro z hz v w
  have hzN : space a s z ∈ N.cylinderDomain := ⟨mem_univ _, hsub hz⟩
  have hf := (N.coordinate_map_smooth.contMDiffAt
    (N.cylinderDomain_open.mem_nhds hzN)).mdifferentiableAt (by simp)
  rw [metric_pullback_affine h N.coordinate_map a s z hf]

variable (h : RiemannianMetric 3 M) (D : LeviCivitaData h)
  (hδ : 0 < δ) (hδhalf : δ < 1 / 2) (q : UnitTwoSphere)
  (hR : 0 < D.scalarCurvature (N.coordinate_map (q, s)))
  (hclose : RoundCylinderClose δ 0 (fun z v w =>
    D.scalarCurvature (N.coordinate_map (q, s)) *
      roundCylinderPullback h (N.coordinate_map ∘ space a s) z v w))


def affineWithMetric : EpsilonNeck h := by
  let e := N.affineCoordinate ha s hsub
  have hsource : e.source = univ ×ˢ Ioo (-δ⁻¹) δ⁻¹ := rfl
  have hpow : ((D.scalarCurvature (N.coordinate_map (q, s))) ^ (-1 / 2 : ℝ))⁻¹ ^ 2 =
      D.scalarCurvature (N.coordinate_map (q, s)) := by
    rw [neg_div, Real.rpow_neg hR.le, inv_inv, ← Real.rpow_natCast,
      ← Real.rpow_mul hR.le]
    norm_num
  refine {
    epsilon := δ
    epsilon_pos := hδ
    epsilon_lt_half := hδhalf
    scale := D.scalarCurvature (N.coordinate_map (q, s)) ^ (-1 / 2 : ℝ)
    scale_pos := Real.rpow_pos_of_pos hR _
    center := N.coordinate_map (q, s)
    connection := D
    scalar_center_pos := hR
    scale_eq_scalar := rfl
    carrier := e.target
    carrier_open := e.open_target
    coordinate := neckDomainCoordinates e hsource
    coordinate_map := N.coordinate_map ∘ space a s
    coordinate_map_eq := fun _ => rfl
    coordinate_map_smooth := N.coordinate_map_smooth.comp (contMDiff_space a s).contMDiffOn
      (fun _ hz => ⟨mem_univ _, hsub hz.2⟩)
    coordinate_inverse := inverseSpace a s ∘ N.coordinate_inverse
    coordinate_inverse_mem := fun _ hx => neckDomainCoordinates_inverse_mem e hsource hx
    coordinate_inverse_left := neckDomainCoordinates_inverse_left e hsource
    coordinate_inverse_right := neckDomainCoordinates_inverse_right e hsource
    coordinate_inverse_smooth := (contMDiff_inverseSpace a s).comp_contMDiffOn
      (N.coordinate_inverse_smooth.mono (fun _ hx => hx.1))
    central_sphere := (N.coordinate_map ∘ space a s) '' (univ ×ˢ ({0} : Set ℝ))
    central_sphere_eq := rfl
    center_on_central_sphere := ?_
    central_sphere_subset := ?_
    metric_comparison := ⟨by simpa only [hpow] using hclose⟩ }
  · exact ⟨(q, 0), ⟨mem_univ _, mem_singleton _⟩, by simp [space]⟩
  · rintro _ ⟨z, hz, rfl⟩
    apply e.map_source
    refine ⟨mem_univ _, ?_⟩
    rw [show z.2 = 0 from hz.2]
    exact ⟨neg_neg_of_pos (inv_pos.mpr hδ), inv_pos.mpr hδ⟩

theorem affineWithMetric_carrier :
    (N.affineWithMetric ha s hsub h D hδ hδhalf q hR hclose).carrier =
      N.region (a * (-δ⁻¹) + s) (a * δ⁻¹ + s) := rfl

theorem affineWithMetric_epsilon :
    (N.affineWithMetric ha s hsub h D hδ hδhalf q hR hclose).epsilon = δ := rfl

theorem affineWithMetric_connection :
    (N.affineWithMetric ha s hsub h D hδ hδhalf q hR hclose).connection = D := rfl

theorem affineWithMetric_scale :
    (N.affineWithMetric ha s hsub h D hδ hδhalf q hR hclose).scale =
      D.scalarCurvature (N.coordinate_map (q, s)) ^ (-1 / 2 : ℝ) := rfl

theorem affineWithMetric_coordinate_map :
    (N.affineWithMetric ha s hsub h D hδ hδhalf q hR hclose).coordinate_map =
      N.coordinate_map ∘ space a s := rfl

theorem affineWithMetric_coordinate_inverse :
    (N.affineWithMetric ha s hsub h D hδ hδhalf q hR hclose).coordinate_inverse =
      inverseSpace a s ∘ N.coordinate_inverse := rfl

theorem affineWithMetric_center :
    (N.affineWithMetric ha s hsub h D hδ hδhalf q hR hclose).center =
      N.coordinate_map (q, s) := rfl

theorem affineWithMetric_central_sphere :
    (N.affineWithMetric ha s hsub h D hδ hδhalf q hR hclose).central_sphere =
      range (fun p : UnitTwoSphere => N.coordinate_map (p, s)) := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨z.1, ?_⟩
    simp only [Function.comp_apply, space, show z.2 = 0 from hz.2, mul_zero, zero_add]
  · rintro ⟨p, rfl⟩
    exact ⟨(p, 0), ⟨mem_univ _, mem_singleton _⟩, by simp [space]⟩

theorem affineWithMetric_region (l r : ℝ) :
    (N.affineWithMetric ha s hsub h D hδ hδhalf q hR hclose).region l r =
      N.region (a * (-δ⁻¹) + s) (a * δ⁻¹ + s) ∩ N.region (a * l + s) (a * r + s) := by
  ext x
  change (x ∈ N.region (a * (-δ⁻¹) + s) (a * δ⁻¹ + s) ∧
    l < ((N.coordinate_inverse x).2 - s) / a ∧
    ((N.coordinate_inverse x).2 - s) / a < r) ↔ _
  rw [lt_div_iff₀ ha, div_lt_iff₀ ha]
  constructor
  · intro hx
    exact ⟨hx.1, hx.1.1, by nlinarith [hx.2.1], by nlinarith [hx.2.2]⟩
  · intro hx
    exact ⟨hx.1, by nlinarith [hx.2.2.1], by nlinarith [hx.2.2.2]⟩

theorem affineWithMetric_region_of_bounds {l r : ℝ} (hl : -δ⁻¹ ≤ l) (hr : r ≤ δ⁻¹) :
    (N.affineWithMetric ha s hsub h D hδ hδhalf q hR hclose).region l r =
      N.region (a * l + s) (a * r + s) := by
  rw [N.affineWithMetric_region ha s hsub h D hδ hδhalf q hR hclose]
  apply inter_eq_right.mpr
  intro x hx
  refine ⟨hx.1, ?_, ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_left hl ha.le, hx.2.1]
  · nlinarith [mul_le_mul_of_nonneg_left hr ha.le, hx.2.2]

end PoincareConjecture.EpsilonNeck
