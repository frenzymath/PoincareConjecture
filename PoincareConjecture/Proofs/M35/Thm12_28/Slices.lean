import PoincareConjecture.Definitions.Ch12.StandardCap
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Metric.LocalDiffeomorph
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Connection.OpenDomain

set_option autoImplicit false

open Set TopologicalSpace
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.OrdinaryRealization

def sliceDomain (J : Set ℝ) (t : ℝ) : Opens StandardCapSpace :=
  ⟨{_x : StandardCapSpace | t ∈ J}, by
    by_cases ht : t ∈ J
    · simpa only [ht, ofPred_true] using isOpen_univ (X := StandardCapSpace)
    · simpa only [ht, ofPred_false] using isOpen_empty (X := StandardCapSpace)⟩

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

def sliceDiffeomorph {J : Set ℝ} {t : ℝ} (ht : t ∈ J) :
    Diffeomorph (𝓡 3) (𝓡 3) (slice J t).carrier StandardCapSpace ∞ where
  toFun := Subtype.val
  invFun x := ⟨x, ht⟩
  left_inv _ := rfl
  right_inv _ := rfl
  contMDiff_toFun := contMDiff_subtype_val
  contMDiff_invFun :=
    (ContMDiff.subtypeVal_comp_iff (sliceDomain J t) (fun x => ⟨x, ht⟩)).mp contMDiff_id

theorem slice_val_localDiffeomorph (J : Set ℝ) (t : ℝ) :
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞
      (Subtype.val : (slice J t).carrier → StandardCapSpace) := by
  intro x
  exact (sliceDiffeomorph x.property).isLocalDiffeomorph x

noncomputable def metric {J : Set ℝ} (F : RicciFlow 3 StandardCapSpace J) (t : ℝ) :
    RiemannianMetric 3 (slice J t).carrier :=
  (F.metric t).pullbackOfLocalDiffeomorph Subtype.val (slice_val_localDiffeomorph J t)

noncomputable def connection {J : Set ℝ} (F : RicciFlow 3 StandardCapSpace J) (t : ℝ) :
    LeviCivitaData (metric F t) :=
  (metric F t).openEuclideanLeviCivitaData (sliceDomain J t)

theorem slice_nonempty_iff (J : Set ℝ) (t : ℝ) :
    Nonempty (slice J t).carrier ↔ t ∈ J := by
  constructor
  · rintro ⟨x⟩
    exact x.property
  · intro ht
    exact ⟨⟨0, ht⟩⟩

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

end PoincareConjecture.M35.OrdinaryRealization
