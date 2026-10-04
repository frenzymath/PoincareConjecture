import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Neck
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiff.Constructions

/-!
Adapted from Mapher `PoincareMT/Proofs/M49/NeckCoordinates.lean` at
revision `f927d9e1f0810042766d3b5f64d3f4da02ee93cc`.

# The actual neck as a smooth Euclidean partial chart

Morgan-Tian Definition 2.18, p. 31. These coordinate adapters expand
the neck-volume argument used in Lemma 17.12, p. 410. The chart maps
remain the frozen coordinate map and inverse, composed with an actual
sphere chart and a fixed continuous linear coordinate splitting.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareMT.SurgeryVolume

/-- Split the three Euclidean coordinates into two sphere coordinates
and one line coordinate (MT Definition 2.18, p. 31). -/
noncomputable def cylinderCoordinateEquiv :
    EuclideanSpace ℝ (Fin 3) ≃L[ℝ] RoundCylinderCoordinates :=
  EuclideanSpace.finAddEquivProd.trans
    ((ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin 2))).prodCongr
      (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)))

/-- The splitting keeps the first two coordinates and the last coordinate
in their displayed order (MT Definition 2.18, p. 31). -/
theorem cylinderCoordinateEquiv_apply (x : EuclideanSpace ℝ (Fin 3)) :
    cylinderCoordinateEquiv x = (WithLp.toLp 2 ![x 0, x 1], x 2) := by
  apply Prod.ext
  · ext i
    fin_cases i <;> rfl
  · rfl

/-- The splitting sends the standard basis to the literal frozen
cylinder coordinate basis (MT Definition 2.18, p. 31). -/
theorem cylinderCoordinateEquiv_basis (i : Fin 3) :
    cylinderCoordinateEquiv (EuclideanSpace.basisFun (Fin 3) ℝ i) =
      roundCylinderCoordinateBasis i := by
  rw [cylinderCoordinateEquiv_apply]
  fin_cases i
  · apply Prod.ext
    · ext j
      fin_cases j <;> simp [roundCylinderCoordinateBasis, EuclideanSpace.basisFun_apply]
    · simp [roundCylinderCoordinateBasis, EuclideanSpace.basisFun_apply]
  · apply Prod.ext
    · ext j
      fin_cases j <;> simp [roundCylinderCoordinateBasis, EuclideanSpace.basisFun_apply]
    · simp [roundCylinderCoordinateBasis, EuclideanSpace.basisFun_apply]
  · simp [roundCylinderCoordinateBasis, EuclideanSpace.basisFun_apply]

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

/-- The actual neck coordinate and inverse define an open partial
homeomorphism on the specified cylinder (MT Definition 2.18, p. 31). -/
def epsilonNeckChart (N : EpsilonNeck g) :
    OpenPartialHomeomorph RoundCylinderSpace M where
  toFun := N.coordinate_map
  invFun := N.coordinate_inverse
  source := univ ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹
  target := N.carrier
  map_source' := by
    intro z hz
    have h := (N.coordinate (z.1, ⟨z.2, hz.2⟩)).property
    simpa only [N.coordinate_map_eq] using h
  map_target' := N.coordinate_inverse_mem
  left_inv' := by
    intro z hz
    have h := N.coordinate_inverse_left (z.1, ⟨z.2, hz.2⟩)
    simpa only [N.coordinate_map_eq] using h
  right_inv' := by
    intro x hx
    have h := congrArg Subtype.val (N.coordinate_inverse_right x hx)
    simpa only [N.coordinate_map_eq] using h
  open_source := isOpen_univ.prod isOpen_Ioo
  open_target := N.carrier_open
  continuousOn_toFun := N.coordinate_map_smooth.continuousOn
  continuousOn_invFun := N.coordinate_inverse_smooth.continuousOn

/-- Every subinterval of the neck gives exactly its frozen region,
including empty intervals (MT Definition 2.18, p. 31). -/
theorem epsilonNeckChart_image_region (N : EpsilonNeck g) (a b : ℝ)
    (ha : -N.epsilon⁻¹ ≤ a) (hb : b ≤ N.epsilon⁻¹) :
    epsilonNeckChart N '' (univ ×ˢ Ioo a b) = N.region a b := by
  let e := epsilonNeckChart N
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hzs : z ∈ e.source := ⟨mem_univ _, ha.trans_lt hz.2.1, hz.2.2.trans_le hb⟩
    refine ⟨e.map_source hzs, ?_⟩
    change a < (e.symm (e z)).2 ∧ (e.symm (e z)).2 < b
    rw [e.left_inv hzs]
    exact hz.2
  · intro hx
    exact ⟨e.symm x, ⟨mem_univ _, hx.2⟩, e.right_inv hx.1⟩

/-- Compose the actual neck with an actual sphere chart and the fixed
Euclidean splitting (MT Definition 2.18, p. 31). -/
noncomputable def epsilonNeckEuclideanChart (N : EpsilonNeck g) (q : UnitTwoSphere) :
    OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 3)) M :=
  (cylinderCoordinateEquiv.toHomeomorph.toOpenPartialHomeomorph.trans
    ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm.prod
      (OpenPartialHomeomorph.refl ℝ))).trans (epsilonNeckChart N)

/-- The Euclidean neck chart has exactly the chart-target times interval
domain (MT Definition 2.18, p. 31). -/
theorem epsilonNeckEuclideanChart_source (N : EpsilonNeck g) (q : UnitTwoSphere) :
    (epsilonNeckEuclideanChart N q).source = cylinderCoordinateEquiv ⁻¹'
      ((chartAt (EuclideanSpace ℝ (Fin 2)) q).target ×ˢ
        Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) := by
  ext x
  simp [epsilonNeckEuclideanChart, epsilonNeckChart]

/-- The displayed Euclidean neck chart is smooth on its actual source
(MT Definition 2.18, p. 31). -/
theorem epsilonNeckEuclideanChart_contMDiffOn (N : EpsilonNeck g) (q : UnitTwoSphere) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (epsilonNeckEuclideanChart N q)
      (epsilonNeckEuclideanChart N q).source := by
  let c := chartAt (EuclideanSpace ℝ (Fin 2)) q
  intro x hx
  have hx0 : (cylinderCoordinateEquiv x).1 ∈ c.target ∧
      (cylinderCoordinateEquiv x).2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
    simpa only [epsilonNeckEuclideanChart_source, mem_preimage, mem_prod] using hx
  have hfirst : ContMDiffAt (𝓡 3) (𝓡 2) ∞
      (fun y => (cylinderCoordinateEquiv y).1) x :=
    (contDiff_fst.comp cylinderCoordinateEquiv.contDiff).contMDiff.contMDiffAt
  have hsecond : ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) ∞
      (fun y => (cylinderCoordinateEquiv y).2) x :=
    (contDiff_snd.comp cylinderCoordinateEquiv.contDiff).contMDiff.contMDiffAt
  have hcs : ContMDiffAt (𝓡 2) (𝓡 2) ∞ c.symm (cylinderCoordinateEquiv x).1 :=
    contMDiffOn_chart_symm.contMDiffAt (c.open_target.mem_nhds hx0.1)
  have hpair := (hcs.comp x hfirst).prodMk hsecond
  have hN : ContMDiffAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ N.coordinate_map
      (c.symm (cylinderCoordinateEquiv x).1, (cylinderCoordinateEquiv x).2) :=
    N.coordinate_map_smooth.contMDiffAt
      ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, hx0.2⟩)
  exact (hN.comp x hpair).contMDiffWithinAt

/-- The displayed inverse Euclidean neck chart is smooth on its actual
target (MT Definition 2.18, p. 31). -/
theorem epsilonNeckEuclideanChart_symm_contMDiffOn
    (N : EpsilonNeck g) (q : UnitTwoSphere) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (epsilonNeckEuclideanChart N q).symm
      (epsilonNeckEuclideanChart N q).target := by
  let c := chartAt (EuclideanSpace ℝ (Fin 2)) q
  intro y hy
  have hy0 : y ∈ N.carrier ∧ (N.coordinate_inverse y).1 ∈ c.source := by
    simpa [epsilonNeckEuclideanChart, epsilonNeckChart] using hy
  have hi : ContMDiffAt (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ N.coordinate_inverse y :=
    N.coordinate_inverse_smooth.contMDiffAt (N.carrier_open.mem_nhds hy0.1)
  have hc : ContMDiffAt (𝓡 2) (𝓡 2) ∞ c (N.coordinate_inverse y).1 :=
    contMDiffOn_chart.contMDiffAt (c.open_source.mem_nhds hy0.2)
  have hpair := (hc.comp y hi.fst).prodMk_space hi.snd
  exact (cylinderCoordinateEquiv.symm.contDiff.contMDiff.contMDiffAt.comp y
    hpair).contMDiffWithinAt

end PoincareMT.SurgeryVolume
