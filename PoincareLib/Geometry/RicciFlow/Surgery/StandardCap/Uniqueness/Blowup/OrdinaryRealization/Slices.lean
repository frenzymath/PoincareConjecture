import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Imports
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Geometry
import PoincareLib.Geometry.Riemannian.Metric.LocalDiffeomorph
import PoincareLib.Geometry.Riemannian.Connection.OpenDomain

/-!
# Actual ordinary slices for the standard-flow blowup argument

Morgan-Tian, Theorem 12.28, printed pp. 323-324, uses the Chapter 11
generalized flow attached to the ordinary standard flow. The slices here
are canonically the original space at valid times and empty at other times.
See `proof-work/tasks/M35/derivations/04-generalized-realization.md`.
-/

set_option autoImplicit false

open Set TopologicalSpace
open scoped Manifold ContDiff Bundle Topology

namespace PoincareMT.M35.OrdinaryRealization

/-- Chapter 11 realization for Theorem 12.28, pp. 323-324: retain only valid time slices. -/
def sliceDomain (J : Set ℝ) (t : ℝ) : Opens StandardCapSpace :=
  ⟨{_x : StandardCapSpace | t ∈ J}, by
    by_cases ht : t ∈ J
    · simpa only [ht, ofPred_true] using isOpen_univ (X := StandardCapSpace)
    · simpa only [ht, ofPred_false] using isOpen_empty (X := StandardCapSpace)⟩

/-- Every retained ordinary slice has its inherited manifold and Borel structures.
Used in Theorem 12.28, pp. 323-324. -/
noncomputable def slice (J : Set ℝ) (t : ℝ) : GeneralizedSliceCarrier where
  carrier := sliceDomain J t
  topologicalSpace := inferInstance
  measurableSpace := inferInstance
  borelSpace := inferInstance
  chartedSpace := inferInstance
  isManifold := inferInstance
  t2Space := inferInstance
  t3Space := inferInstance
  secondCountable := inferInstance

/-- A valid slice identifies smoothly with the original ordinary carrier.
Used in Theorem 12.28, pp. 323-324. -/
def sliceDiffeomorph {J : Set ℝ} {t : ℝ} (ht : t ∈ J) :
    Diffeomorph (𝓡 3) (𝓡 3) (slice J t).carrier StandardCapSpace ∞ where
  toFun := Subtype.val
  invFun x := ⟨x, ht⟩
  left_inv _ := rfl
  right_inv _ := rfl
  contMDiff_toFun := contMDiff_subtype_val
  contMDiff_invFun :=
    (ContMDiff.subtypeVal_comp_iff (sliceDomain J t) (fun x => ⟨x, ht⟩)).mp contMDiff_id

/-- Inclusion of each slice is a local diffeomorphism, also on an empty slice.
Used in Theorem 12.28, pp. 323-324. -/
theorem slice_val_localDiffeomorph (J : Set ℝ) (t : ℝ) :
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞
      (Subtype.val : (slice J t).carrier → StandardCapSpace) := by
  intro x
  exact (sliceDiffeomorph x.property).isLocalDiffeomorph x

/-- The selected metric on a retained slice is the original metric's actual pullback.
Used in Theorem 12.28, pp. 323-324. -/
noncomputable def metric {J : Set ℝ} (F : RicciFlow 3 StandardCapSpace J) (t : ℝ) :
    RiemannianMetric 3 (slice J t).carrier :=
  (F.metric t).pullbackOfLocalDiffeomorph Subtype.val (slice_val_localDiffeomorph J t)

/-- Compatible connection data on the actual selected slice metric, for
Theorem 12.28, pp. 323-324. Curvature
transport to F is proved using the local-isometry identities, not record equality. -/
noncomputable def connection {J : Set ℝ} (F : RicciFlow 3 StandardCapSpace J) (t : ℝ) :
    LeviCivitaData (metric F t) :=
  (metric F t).openEuclideanLeviCivitaData (sliceDomain J t)

/-- The Chapter 11 carrier is nonempty exactly on the ordinary flow's interval.
Used in Theorem 12.28, pp. 323-324. -/
theorem slice_nonempty_iff (J : Set ℝ) (t : ℝ) :
    Nonempty (slice J t).carrier ↔ t ∈ J := by
  constructor
  · rintro ⟨x⟩
    exact x.property
  · intro ht
    exact ⟨⟨0, ht⟩⟩

/-- The box-to-slice map recovers the original metric, with the actual derivative.
Used in Theorem 12.28, pp. 323-324. -/
theorem metric_pullback {J : Set ℝ} (F : RicciFlow 3 StandardCapSpace J)
    {t : ℝ} (ht : t ∈ J) (x : StandardCapSpace) (u v : TangentSpace (𝓡 3) x) :
    (metric F t).inner ((sliceDiffeomorph ht).symm x)
      (mfderiv (𝓡 3) (𝓡 3) (sliceDiffeomorph ht).symm x u)
      (mfderiv (𝓡 3) (𝓡 3) (sliceDiffeomorph ht).symm x v) =
        (F.metric t).inner x u v := by
  let e := sliceDiffeomorph ht
  have hcomp (w : TangentSpace (𝓡 3) x) :
      mfderiv (𝓡 3) (𝓡 3) e (e.symm x)
        (mfderiv (𝓡 3) (𝓡 3) e.symm x w) = w := by
    have hd := mfderiv_comp_apply x (e.contMDiff.mdifferentiable (by simp) _)
      (e.symm.contMDiff.mdifferentiable (by simp) _) w
    have heq : (e : (slice J t).carrier → StandardCapSpace) ∘ e.symm = id :=
      funext e.apply_symm_apply
    have hid : mfderiv (𝓡 3) (𝓡 3) (fun z : StandardCapSpace => z) x w = w := by
      exact congrArg (fun L : TangentSpace (𝓡 3) x →L[ℝ] TangentSpace (𝓡 3) x => L w)
        (mfderiv_id (I := 𝓡 3) (x := x))
    exact hd.symm.trans ((congrArg
      (fun f : StandardCapSpace → StandardCapSpace => mfderiv (𝓡 3) (𝓡 3) f x w) heq).trans hid)
  change (F.metric t).inner (e (e.symm x))
    (mfderiv (𝓡 3) (𝓡 3) e (e.symm x) (mfderiv (𝓡 3) (𝓡 3) e.symm x u))
    (mfderiv (𝓡 3) (𝓡 3) e (e.symm x) (mfderiv (𝓡 3) (𝓡 3) e.symm x v)) = _
  rw [hcomp u, hcomp v, e.apply_symm_apply]

end PoincareMT.M35.OrdinaryRealization
