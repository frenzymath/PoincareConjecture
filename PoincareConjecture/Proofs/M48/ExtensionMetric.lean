import PoincareConjecture.Proofs.M48.ExtensionCylinderMetric
import PoincareConjecture.Proofs.M48.StaticMetric
import PoincareConjecture.Statements.M13Rescaling

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareConjecture.SurgeryFlowExtension

variable {F : SurgeryFlowData.{u}} (E : SurgeryFlowExtension F)

theorem identify_heq {s t : ℝ} (hs : s ∈ F.time_domain) (ht : t ∈ F.time_domain)
    {x : (F.slice s).carrier} {y : (F.slice t).carrier}
    (hst : s = t) (hxy : HEq x y) :
    HEq (E.identify s hs x) (E.identify t ht y) := by
  subst t
  exact heq_of_eq (congrArg (E.identify s hs) (eq_of_heq hxy))

theorem identify_symm_heq {s t : ℝ} (hs : s ∈ F.time_domain) (ht : t ∈ F.time_domain)
    {x : (E.extended.slice s).carrier} {y : (E.extended.slice t).carrier}
    (hst : s = t) (hxy : HEq x y) :
    HEq ((E.identify s hs).symm x) ((E.identify t ht).symm y) := by
  subst t
  exact heq_of_eq (congrArg (E.identify s hs).symm (eq_of_heq hxy))

theorem metric_homothety (t : ℝ) (ht : t ∈ F.time_domain) :
    MetricHomothety (F.metric t) (E.extended.metric t) (E.identify t ht) 1 := by
  intro x v w
  simpa only [one_mul] using E.metric_pullback t ht x v w

theorem metric_homothety_symm (t : ℝ) (ht : t ∈ F.time_domain) :
    MetricHomothety (E.extended.metric t) (F.metric t) (E.identify t ht).symm 1 := by
  let e := E.identify t ht
  intro y v w
  have hcomp : e ∘ e.symm = id := by
    funext z
    exact e.apply_symm_apply z
  have hd := mfderiv_comp y (e.contMDiff.mdifferentiable (by simp) (e.symm y))
    (e.symm.contMDiff.mdifferentiable (by simp) y)
  rw [hcomp, mfderiv_id] at hd
  have hv (z : TangentSpace (𝓡 3) y) :
      mfderiv (𝓡 3) (𝓡 3) e (e.symm y)
        (mfderiv (𝓡 3) (𝓡 3) e.symm y z) = z :=
    (congrArg (fun A => A z) hd).symm
  have he := E.metric_pullback t ht (e.symm y)
    (mfderiv (𝓡 3) (𝓡 3) e.symm y v) (mfderiv (𝓡 3) (𝓡 3) e.symm y w)
  change (E.extended.metric t).inner (e (e.symm y))
    (mfderiv (𝓡 3) (𝓡 3) e (e.symm y) (mfderiv (𝓡 3) (𝓡 3) e.symm y v))
    (mfderiv (𝓡 3) (𝓡 3) e (e.symm y) (mfderiv (𝓡 3) (𝓡 3) e.symm y w)) = _ at he
  rw [hv v, hv w, e.apply_symm_apply] at he
  simpa only [one_mul] using he.symm

theorem metric_calculus (m13 : GeneralizedParabolicRescalingTheory.{u} 3)
    (t : ℝ) (ht : t ∈ F.time_domain) :
    MetricHomothetyCalculus (F.metric t) (E.extended.metric t) (E.identify t ht) 1 :=
  m13.metric_homothety _ _ _ _ _ 1 (by norm_num) (E.metric_homothety t ht)

theorem metric_calculus_symm (m13 : GeneralizedParabolicRescalingTheory.{u} 3)
    (t : ℝ) (ht : t ∈ F.time_domain) :
    MetricHomothetyCalculus (E.extended.metric t) (F.metric t) (E.identify t ht).symm 1 :=
  m13.metric_homothety _ _ _ _ _ 1 (by norm_num) (E.metric_homothety_symm t ht)

theorem positive_component (m13 : GeneralizedParabolicRescalingTheory.{u} 3)
    (t : ℝ) (ht : t ∈ F.time_domain) (x : (F.slice t).carrier)
    (hpositive : SurgeryPositiveComponentAt F t x) :
    SurgeryPositiveComponentAt E.extended t (E.identify t ht x) := by
  let e := E.identify t ht
  have H : MetricHomothetyCalculus (E.extended.metric t) (F.metric t) e.symm 1 :=
    E.metric_calculus_symm m13 t ht
  have he : MetricHomothety (E.extended.metric t) (F.metric t) e.symm 1 :=
    E.metric_homothety_symm t ht
  intro y hy v w hpair
  have hyold : e.symm y ∈ connectedComponent x := by
    have h := e.symm.continuous.mapsTo_connectedComponent (e x) hy
    simpa only [e.symm_apply_apply] using h
  have hpairOld : LeviCivitaData.IsOrthonormalPair (F.metric t) (e.symm y)
      (mfderiv (𝓡 3) (𝓡 3) e.symm y v) (mfderiv (𝓡 3) (𝓡 3) e.symm y w) := by
    simpa only [LeviCivitaData.IsOrthonormalPair, he y v v, he y w w,
      he y v w, one_mul] using hpair
  have h := hpositive (e.symm y) hyold _ _ hpairOld
  simpa only [H.sectional_eq (E.extended.connection t) (F.connection t), div_one] using h

end PoincareConjecture.SurgeryFlowExtension
