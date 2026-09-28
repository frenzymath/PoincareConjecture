import PoincareConjecture.Proofs.M02.Topology.IntegralOrientationCover
import PoincareConjecture.Proofs.M02.Topology.IntegralHomologyUniverse
import PoincareConjecture.Proofs.M02.Topology.IntegralConvexSupport
import Mathlib.Geometry.Manifold.ChartedSpace









set_option autoImplicit false

noncomputable section

open CategoryTheory Limits HomologicalComplex Set Metric
open scoped Topology

universe u v

namespace PoincareConjecture.Proofs.M02.Topology

theorem integralChartSupportRestriction_homology_isIso
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y] (e : OpenPartialHomeomorph X Y) {K L : Set X}
    (hK : IsCompact K) (hL : IsCompact L) (hKs : K ⊆ e.source)
    (hLs : L ⊆ e.source) (hLK : L ⊆ K) (n : Nat)
    (h : IsIso (integralSupportHomologyRestriction (image_mono (f := e) hLK) n)) :
    IsIso (integralSupportHomologyRestriction hLK n) := by
  let EK := integralChartSupportHomologyEquiv e K hK hKs n
  let EL := integralChartSupportHomologyEquiv e L hL hLs n
  have hr := (ConcreteCategory.isIso_iff_bijective
    (integralSupportHomologyRestriction (image_mono (f := e) hLK) n)).mp h
  rw [ConcreteCategory.isIso_iff_bijective]
  constructor
  · intro a b hab
    apply EK.injective
    apply hr.injective
    rw [← integralChartSupportHomologyEquiv_naturality e hK hL hKs hLs hLK n a,
      ← integralChartSupportHomologyEquiv_naturality e hK hL hKs hLs hLK n b, hab]
  · intro b
    obtain ⟨c, hc⟩ := hr.surjective (EL b)
    refine ⟨EK.symm c, EL.injective ?_⟩
    rw [integralChartSupportHomologyEquiv_naturality e hK hL hKs hLs hLK n,
      LinearEquiv.apply_symm_apply]
    exact hc

theorem exists_integralThreeChartSupport
    {X : Type u} [TopologicalSpace X] [T2Space X]
    (e : OpenPartialHomeomorph X (EuclideanSpace Real (Fin 3)))
    (x : X) (hx : x ∈ e.source) :
    ∃ K U : Set X, IsCompact K ∧ IsOpen U ∧ x ∈ U ∧ ∃ hUK : U ⊆ K,
      Nonempty (Int ≃ₗ[Int] integralSupportHomology K 3) ∧
      ∀ y : X, ∀ hy : y ∈ U,
        IsIso (integralSupportHomologyRestriction
          (singleton_subset_iff.mpr (hUK hy)) 3) := by
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (e.open_target.mem_nhds (e.map_source hx))
  let B := closedBall (e x) r
  let K := e.symm '' B
  let U := e.source ∩ e ⁻¹' ball (e x) r
  have hB : IsCompact B := isCompact_closedBall (e x) r
  have hK : IsCompact K := hB.image_of_continuousOn (e.symm.continuousOn.mono hball)
  have hKs : K ⊆ e.source := by
    rintro y ⟨z, hz, rfl⟩
    exact e.map_target (hball hz)
  have heK : e '' K = B := by
    apply subset_antisymm
    · rintro z ⟨y, ⟨w, hw, rfl⟩, rfl⟩
      simpa only [e.right_inv (hball hw)] using hw
    · intro z hz
      exact ⟨e.symm z, ⟨z, hz, rfl⟩, e.right_inv (hball hz)⟩
  have hU : IsOpen U := e.isOpen_inter_preimage isOpen_ball
  have hxU : x ∈ U := ⟨hx, mem_ball_self hr⟩
  have hUK : U ⊆ K := by
    intro y hy
    exact ⟨e y, ball_subset_closedBall hy.2, e.left_inv hy.1⟩
  have hconv : Convex Real (e '' K) := by
    rw [heK]
    exact convex_closedBall (e x) r
  have himage : IsCompact (e '' K) := by
    rw [heK]
    exact hB
  have hex : e x ∈ e '' K := mem_image_of_mem e (hUK hxU)
  let eZ : integralSupportHomology K 3 ≃ₗ[Int] Int :=
    (integralChartSupportHomologyEquiv e K hK hKs 3).trans
      ((integralEuclideanCompactConvexSupportThreeIso (e '' K) himage hconv (e x)
        hex).toLinearEquiv.trans
        ULift.moduleEquiv)
  refine ⟨K, U, hK, hU, hxU, hUK, ⟨eZ.symm⟩, ?_⟩
  intro y hy
  apply integralChartSupportRestriction_homology_isIso e hK isCompact_singleton hKs
    (singleton_subset_iff.mpr hy.1) (singleton_subset_iff.mpr (hUK hy)) 3
  have hi := integralCompactConvexSupportRestriction_homology_isIso (e '' K) himage hconv
    (e y) (mem_image_of_mem e (hUK hy)) 3
  have himg (S : Set (EuclideanSpace Real (Fin 3))) (hS : S ⊆ e '' K)
      (hSpoint : S = {e y}) : IsIso (integralSupportHomologyRestriction hS 3) := by
    subst S
    exact hi
  exact himg _ _ image_singleton

theorem exists_integralThreeLocalHomologyAtlas
    {X : Type u} [TopologicalSpace X] [T2Space X]
    [ChartedSpace (EuclideanSpace Real (Fin 3)) X] :
    Nonempty (IntegralLocalHomologyAtlas X 3) := by
  classical
  choose K U hK hU hxU hUK hb hr using fun x : X =>
    exists_integralThreeChartSupport (chartAt (EuclideanSpace Real (Fin 3)) x) x
      (mem_chart_source _ x)
  exact ⟨{ support := K
           baseSet := U
           isOpen_baseSet := hU
           mem_baseSet := hxU
           baseSet_subset_support := hUK
           basis := fun x => Classical.choice (hb x)
           restriction_isIso := hr }⟩

theorem exists_integralThreeLocallyRepresentedGenerators
    {X : Type u} [TopologicalSpace X] [T2Space X]
    [ChartedSpace (EuclideanSpace Real (Fin 3)) X]
    [SimplyConnectedSpace X] (x0 : X) :
    ∃ omega : ∀ x : X, integralSupportHomology ({x} : Set X) 3,
      (∀ x : X, ∃ e : Int ≃ₗ[Int] integralSupportHomology ({x} : Set X) 3,
        e 1 = omega x) ∧
      ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
        ∃ b : integralSupportHomology U 3,
          ∀ y : X, ∀ hy : y ∈ U,
            integralSupportHomologyRestriction (singleton_subset_iff.mpr hy) 3 b = omega y := by
  let : LocallyPathConnectedSpace X :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace Real (Fin 3)) X
  obtain ⟨A⟩ := exists_integralThreeLocalHomologyAtlas (X := X)
  exact A.exists_locallyRepresented_generators x0

end PoincareConjecture.Proofs.M02.Topology
