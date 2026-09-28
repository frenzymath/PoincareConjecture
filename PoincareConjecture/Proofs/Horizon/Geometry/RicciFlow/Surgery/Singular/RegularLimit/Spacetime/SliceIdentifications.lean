import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Spacetime.Carrier








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology

universe u

noncomputable section

namespace PoincareConjecture.SingularRegularLimit.SliceGeometry

variable {G K : SliceGeometry.{u}}

def homeomorphOfEq (h : G = K) : G.slice.carrier ≃ₜ K.slice.carrier := by
  subst K
  exact Homeomorph.refl _

@[simp] theorem homeomorphOfEq_refl (G : SliceGeometry.{u}) :
    homeomorphOfEq (rfl : G = G) = Homeomorph.refl _ := rfl

@[simp] theorem homeomorphOfEq_symm (h : G = K) :
    (homeomorphOfEq h).symm = homeomorphOfEq h.symm := by
  subst K
  rfl

theorem homeomorphOfEq_smooth (h : G = K) :
    ContMDiff (𝓡 3) (𝓡 3) ∞ (homeomorphOfEq h) := by
  subst K
  exact contMDiff_id

theorem homeomorphOfEq_symm_smooth (h : G = K) :
    ContMDiff (𝓡 3) (𝓡 3) ∞ (homeomorphOfEq h).symm := by
  rw [homeomorphOfEq_symm]
  exact homeomorphOfEq_smooth h.symm

theorem homeomorphOfEq_mfderiv_bijective (h : G = K) (x : G.slice.carrier) :
    Function.Bijective (mfderiv (𝓡 3) (𝓡 3) (homeomorphOfEq h) x) := by
  subst K
  change Function.Bijective (mfderiv (𝓡 3) (𝓡 3) id x)
  rw [mfderiv_id]
  exact ⟨fun _ _ h => h, fun y => ⟨y, rfl⟩⟩

theorem homeomorphOfEq_metric_pullback (h : G = K) (x : G.slice.carrier)
    (v w : TangentSpace (𝓡 3) x) :
    K.metric.inner (homeomorphOfEq h x)
      (mfderiv (𝓡 3) (𝓡 3) (homeomorphOfEq h) x v)
      (mfderiv (𝓡 3) (𝓡 3) (homeomorphOfEq h) x w) = G.metric.inner x v w := by
  subst K
  change G.metric.inner x (mfderiv (𝓡 3) (𝓡 3) id x v)
    (mfderiv (𝓡 3) (𝓡 3) id x w) = _
  rw [mfderiv_id]
  rfl

theorem homeomorphOfEq_scalar_pullback (h : G = K) (x : G.slice.carrier) :
    K.connection.scalarCurvature (homeomorphOfEq h x) = G.connection.scalarCurvature x := by
  subst K
  rfl

end PoincareConjecture.SingularRegularLimit.SliceGeometry

namespace PoincareConjecture.SingularTimeAssumptions

open SingularRegularLimit

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}


def oldSliceHomeomorph (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) {t : ℝ} (ht : t ≠ T) :
    (F.slice t).carrier ≃ₜ (H.extendedSliceGeometry P04 t).slice.carrier :=
  SliceGeometry.homeomorphOfEq (H.extendedSliceGeometry_of_ne P04 ht).symm

theorem oldSliceHomeomorph_smooth (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) {t : ℝ} (ht : t ≠ T) :
    ContMDiff (𝓡 3) (𝓡 3) ∞ (H.oldSliceHomeomorph P04 ht) :=
  SliceGeometry.homeomorphOfEq_smooth (H.extendedSliceGeometry_of_ne P04 ht).symm

theorem oldSliceHomeomorph_symm_smooth (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) {t : ℝ} (ht : t ≠ T) :
    ContMDiff (𝓡 3) (𝓡 3) ∞ (H.oldSliceHomeomorph P04 ht).symm :=
  SliceGeometry.homeomorphOfEq_symm_smooth (H.extendedSliceGeometry_of_ne P04 ht).symm

theorem oldSliceHomeomorph_metric_pullback (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) {t : ℝ} (ht : t ≠ T)
    (x : (F.slice t).carrier) (v w : TangentSpace (𝓡 3) x) :
    (H.extendedSliceGeometry P04 t).metric.inner (H.oldSliceHomeomorph P04 ht x)
      (mfderiv (𝓡 3) (𝓡 3) (H.oldSliceHomeomorph P04 ht) x v)
      (mfderiv (𝓡 3) (𝓡 3) (H.oldSliceHomeomorph P04 ht) x w) =
        (F.metric t).inner x v w :=
  SliceGeometry.homeomorphOfEq_metric_pullback
    (G := SliceGeometry.ofFlow F t) (K := H.extendedSliceGeometry P04 t)
    (H.extendedSliceGeometry_of_ne P04 ht).symm x v w

theorem oldSliceHomeomorph_scalar_pullback (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) {t : ℝ} (ht : t ≠ T)
    (x : (F.slice t).carrier) :
    (H.extendedSliceGeometry P04 t).connection.scalarCurvature
      (H.oldSliceHomeomorph P04 ht x) = (F.connection t).scalarCurvature x :=
  SliceGeometry.homeomorphOfEq_scalar_pullback
    (G := SliceGeometry.ofFlow F t) (K := H.extendedSliceGeometry P04 t)
    (H.extendedSliceGeometry_of_ne P04 ht).symm x


def terminalSliceHomeomorph (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) :
    (H.extendedSliceGeometry P04 T).slice.carrier ≃ₜ H.regularRegion P04 :=
  SliceGeometry.homeomorphOfEq (H.extendedSliceGeometry_terminal P04)

theorem terminalSliceHomeomorph_smooth (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) :
    ContMDiff (𝓡 3) (𝓡 3) ∞ (H.terminalSliceHomeomorph P04) :=
  SliceGeometry.homeomorphOfEq_smooth (H.extendedSliceGeometry_terminal P04)

theorem terminalSliceHomeomorph_symm_smooth (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) :
    ContMDiff (𝓡 3) (𝓡 3) ∞ (H.terminalSliceHomeomorph P04).symm :=
  SliceGeometry.homeomorphOfEq_symm_smooth (H.extendedSliceGeometry_terminal P04)

theorem terminalSliceHomeomorph_mfderiv_bijective (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u})
    (x : (H.extendedSliceGeometry P04 T).slice.carrier) :
    Function.Bijective (mfderiv (𝓡 3) (𝓡 3) (H.terminalSliceHomeomorph P04) x) :=
  SliceGeometry.homeomorphOfEq_mfderiv_bijective (H.extendedSliceGeometry_terminal P04) x

theorem terminalSliceHomeomorph_metric_pullback (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u})
    (x : (H.extendedSliceGeometry P04 T).slice.carrier) (v w : TangentSpace (𝓡 3) x) :
    (H.terminalMetric P04).inner (H.terminalSliceHomeomorph P04 x)
      (mfderiv (𝓡 3) (𝓡 3) (H.terminalSliceHomeomorph P04) x v)
      (mfderiv (𝓡 3) (𝓡 3) (H.terminalSliceHomeomorph P04) x w) =
        (H.extendedSliceGeometry P04 T).metric.inner x v w :=
  SliceGeometry.homeomorphOfEq_metric_pullback
    (G := H.extendedSliceGeometry P04 T) (K := H.terminalSliceGeometry P04)
    (H.extendedSliceGeometry_terminal P04) x v w

theorem terminalSliceHomeomorph_scalar_pullback (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u})
    (x : (H.extendedSliceGeometry P04 T).slice.carrier) :
    (H.terminalConnection P04).scalarCurvature (H.terminalSliceHomeomorph P04 x) =
      (H.extendedSliceGeometry P04 T).connection.scalarCurvature x :=
  SliceGeometry.homeomorphOfEq_scalar_pullback
    (G := H.extendedSliceGeometry P04 T) (K := H.terminalSliceGeometry P04)
    (H.extendedSliceGeometry_terminal P04) x

end PoincareConjecture.SingularTimeAssumptions
