
import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Connection.LocalRegularity
import Mathlib.Geometry.Manifold.VectorBundle.Tensoriality









noncomputable section

set_option autoImplicit false

open Set Filter Bundle
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}


def coordinateRepresentative (p : M) (Y : (x : M) → TangentSpace (𝓡 n) x)
    (x : M) : EuclideanSpace ℝ (Fin n) :=
  (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) p).continuousLinearMapAt
    ℝ x (Y x)


def constantCoordinateField (p : M) (v : EuclideanSpace ℝ (Fin n))
    (x : M) : TangentSpace (𝓡 n) x :=
  (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) p).symmL ℝ x v

lemma mdifferentiableAt_coordinateRepresentative (p : M)
    {Y : (x : M) → TangentSpace (𝓡 n) x} {x : M}
    (hx : x ∈ (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) p).baseSet)
    (hY : MDifferentiableAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) (T% Y) x) :
    MDifferentiableAt (𝓡 n) (𝓡 n) (coordinateRepresentative p Y) x := by
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) p
  have h := (e.mdifferentiableAt_section_iff (𝓡 n) Y hx).mp hY
  apply h.congr_of_eventuallyEq
  filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
  exact e.continuousLinearMapAt_apply_of_mem ℝ hy (Y y)

lemma contMDiffAt_coordinateRepresentative (p : M)
    {Y : (x : M) → TangentSpace (𝓡 n) x} {x : M}
    (hx : x ∈ (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) p).baseSet)
    (hY : ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% Y) x) :
    ContMDiffAt (𝓡 n) (𝓡 n) ∞ (coordinateRepresentative p Y) x := by
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) p
  have h := (e.contMDiffAt_section_iff (IB := 𝓡 n) (n := ∞) hx).mp hY
  apply h.congr_of_eventuallyEq
  filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
  exact e.continuousLinearMapAt_apply_of_mem ℝ hy (Y y)

lemma contMDiffAt_constantCoordinateField (p : M) (v : EuclideanSpace ℝ (Fin n))
    {x : M}
    (hx : x ∈ (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) p).baseSet) :
    ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% (constantCoordinateField p v)) x := by
  let E := EuclideanSpace ℝ (Fin n)
  let e := trivializationAt E (TangentSpace (𝓡 n)) p
  have hv : ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞
      (fun y : M => TotalSpace.mk' E y v) x := by
    rw [contMDiffAt_totalSpace]
    exact ⟨contMDiffAt_id, by simpa using contMDiffAt_const (c := v)⟩
  exact (e.contMDiffAt_symmL (IB := 𝓡 n) (n := ∞) hx).clm_bundle_apply hv

lemma coordinateRepresentative_constant (p : M) (v : EuclideanSpace ℝ (Fin n))
    {x : M}
    (hx : x ∈ (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) p).baseSet) :
    coordinateRepresentative p (constantCoordinateField p v) x = v := by
  exact Trivialization.continuousLinearMapAt_symmL (R := ℝ) _ hx v


def coordinateConnectionDifference (D : LeviCivitaData g) (p : M)
    (Y : (x : M) → TangentSpace (𝓡 n) x) (x : M) :
    TangentSpace (𝓡 n) x →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  ((trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) p).continuousLinearMapAt
    ℝ x).comp (D.connection Y x) -
      mvfderiv (𝓡 n) (coordinateRepresentative p Y) x

lemma coordinateConnectionDifference_tensorial (D : LeviCivitaData g) (p : M)
    {x : M}
    (hx : x ∈ (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) p).baseSet) :
    TensorialAt (𝓡 n) (EuclideanSpace ℝ (Fin n))
      (fun Y => D.coordinateConnectionDifference p Y x) x := by
  constructor
  · intro f Y hf hY
    have hcoord := mdifferentiableAt_coordinateRepresentative p hx hY
    have hfun : coordinateRepresentative p (f • Y) = f • coordinateRepresentative p Y := by
      funext y
      exact map_smul _ (f y) (Y y)
    rw [coordinateConnectionDifference, hfun,
      D.connection.isCovariantDerivativeOn.leibniz hY hf,
      mvfderiv_smul hf hcoord]
    ext u
    simp [coordinateConnectionDifference, coordinateRepresentative]
    ring
  · intro Y Z hY hZ
    have hYcoord := mdifferentiableAt_coordinateRepresentative p hx hY
    have hZcoord := mdifferentiableAt_coordinateRepresentative p hx hZ
    have hfun : coordinateRepresentative p (Y + Z) =
        coordinateRepresentative p Y + coordinateRepresentative p Z := by
      funext y
      exact map_add _ (Y y) (Z y)
    rw [coordinateConnectionDifference, hfun,
      D.connection.isCovariantDerivativeOn.add hY hZ,
      mvfderiv_add hYcoord hZcoord]
    ext u
    simp [coordinateConnectionDifference]
    abel

private def coordinateConnectionBilinear (D : LeviCivitaData g) (p x : M)
    (hx : x ∈ (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) p).baseSet) :
    EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin n) := by
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) p
  let H := fun u v : EuclideanSpace ℝ (Fin n) => e.continuousLinearMapAt ℝ x
    (D.connection (constantCoordinateField p v) x (e.symmL ℝ x u))
  have hfield (v : EuclideanSpace ℝ (Fin n)) :=
    (contMDiffAt_constantCoordinateField p v hx).mdifferentiableAt (by simp)
  refine LinearMap.mk₂ ℝ H ?_ ?_ ?_ ?_
  · intro u u' v
    simp [H, map_add]
  · intro c u v
    simp [H, map_smul]
  · intro u v v'
    have hfields : constantCoordinateField p (v + v') =
        constantCoordinateField p v + constantCoordinateField p v' := by
      funext y
      exact map_add _ v v'
    simp [H, hfields, D.connection.isCovariantDerivativeOn.add (hfield v) (hfield v')]
  · intro c u v
    have hfields : constantCoordinateField p (c • v) =
        c • constantCoordinateField p v := by
      funext y
      exact map_smul _ c v
    simp [H, hfields, D.connection.isCovariantDerivativeOn.smul_const c (hfield v)]



def coordinateConnectionCoefficient (D : LeviCivitaData g) (p x : M) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) := by
  classical
  exact if hx : x ∈
      (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) p).baseSet then
    LinearMap.toContinuousLinearMap
      (LinearMap.toContinuousLinearMap.toLinearMap.comp (D.coordinateConnectionBilinear p x hx))
    else 0

lemma coordinateConnectionCoefficient_apply (D : LeviCivitaData g) (p : M) {x : M}
    (hx : x ∈ (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) p).baseSet)
    (u v : EuclideanSpace ℝ (Fin n)) :
    D.coordinateConnectionCoefficient p x u v =
      coordinateRepresentative p
        (D.covariantDerivativeOnFields (constantCoordinateField p u) (constantCoordinateField p v))
        x := by
  simp only [coordinateConnectionCoefficient, hx, dif_pos]
  rfl

lemma contMDiffAt_coordinateConnectionCoefficient (D : LeviCivitaData g) (p : M) {x : M}
    (hx : x ∈ (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) p).baseSet) :
    ContMDiffAt (𝓡 n) 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) ∞
      (D.coordinateConnectionCoefficient p) x := by
  apply contMDiffAt_clm_of_apply
  intro u
  apply contMDiffAt_clm_of_apply
  intro v
  have h := contMDiffAt_coordinateRepresentative p hx
    (D.contMDiffAt_covariantDerivativeOnFields
      (contMDiffAt_constantCoordinateField p u hx)
      (contMDiffAt_constantCoordinateField p v hx))
  apply h.congr_of_eventuallyEq
  filter_upwards [(trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) p).open_baseSet.mem_nhds hx]
    with y hy
  exact D.coordinateConnectionCoefficient_apply p hy u v



lemma coordinate_connection_eq (D : LeviCivitaData g) (p : M)
    {Y : (x : M) → TangentSpace (𝓡 n) x} {x : M}
    (hx : x ∈ (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) p).baseSet)
    (hY : MDifferentiableAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) (T% Y) x)
    (u : TangentSpace (𝓡 n) x) :
    (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) p).continuousLinearMapAt
      ℝ x (D.connection Y x u) =
      mvfderiv (𝓡 n) (coordinateRepresentative p Y) x u +
        D.coordinateConnectionCoefficient p x
          ((trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) p).continuousLinearMapAt
            ℝ x u) (coordinateRepresentative p Y x) := by
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) p
  let v := coordinateRepresentative p Y x
  have hW := (contMDiffAt_constantCoordinateField p v hx).mdifferentiableAt (by simp)
  have heq := (D.coordinateConnectionDifference_tensorial p hx).pointwise hY hW
    (e.symmL_continuousLinearMapAt hx (Y x)).symm
  have hconst : coordinateRepresentative p (constantCoordinateField p v) =ᶠ[𝓝 x]
      fun _ => v := by
    filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
    exact coordinateRepresentative_constant p v hy
  have hd : mvfderiv (𝓡 n) (coordinateRepresentative p (constantCoordinateField p v)) x = 0 := by
    unfold mvfderiv
    rw [hconst.mfderiv_eq, hconst.self_of_nhds]
    exact mvfderiv_const v
  have hh := congrArg (fun L => L u) heq
  simp only [coordinateConnectionDifference, sub_apply,
    ContinuousLinearMap.comp_apply, hd, sub_zero] at hh
  rw [D.coordinateConnectionCoefficient_apply p hx]
  change e.continuousLinearMapAt ℝ x (D.connection Y x u) =
    mvfderiv (𝓡 n) (coordinateRepresentative p Y) x u +
    e.continuousLinearMapAt ℝ x (D.connection (constantCoordinateField p v) x
      (e.symmL ℝ x (e.continuousLinearMapAt ℝ x u)))
  rw [e.symmL_continuousLinearMapAt hx u]
  exact sub_eq_iff_eq_add'.mp hh

end PoincareConjecture.LeviCivitaData
