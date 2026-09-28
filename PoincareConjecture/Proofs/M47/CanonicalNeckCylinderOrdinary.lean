import PoincareConjecture.Proofs.M47.PositiveHistoryOrdinary
import PoincareConjecture.Proofs.M47.SeedCylinderClock









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M47



theorem exists_buffered_cylinder_ordinary
    (P : M47Predecessors.{u}) {F : SurgeryFlowData.{u}}
    {C : GeneralizedSliceCarrier.{u}} {origin a b : ℝ} (hab : a < b)
    (U : TopologicalSpace.Opens C.carrier) (hne : (U : Set C.carrier).Nonempty)
    (e : SurgeryFlowCylinder F C origin 1 (Icc a b) U) :
    ∃ G : RicciFlow 3 U (Icc (origin + a) (origin + b)),
      ∀ (s : ℝ) (hs : s ∈ Icc a b) (x : U),
        (∀ v w : TangentSpace (𝓡 3) x,
          (F.metric (origin + s / 1)).inner (e.forward s hs x.val)
            (mfderiv (𝓡 3) (𝓡 3) (fun y : U => e.forward s hs y.val) x v)
            (mfderiv (𝓡 3) (𝓡 3) (fun y : U => e.forward s hs y.val) x w) =
              (G.metric (origin + s / 1)).inner x v w) ∧
        (G.connection (origin + s / 1)).scalarCurvature x =
          (F.connection (origin + s / 1)).scalarCurvature (e.forward s hs x.val) ∧
        (G.connection (origin + s / 1)).curvatureTensorNorm x =
          (F.connection (origin + s / 1)).curvatureTensorNorm (e.forward s hs x.val) := by
  have hmem : MapsTo (fun u : ℝ => b + u) (Icc (a - b) 0) (Icc a b) := by
    intro s hs
    constructor <;> linarith only [hs.1, hs.2]
  have hmono : StrictMonoOn (fun u : ℝ => b + u) (Icc (a - b) 0) :=
    fun _ _ _ _ hst => by simpa only [add_comm] using add_lt_add_left hst b
  have hclock : ∀ s ∈ Icc (a - b) 0,
      (origin + b) + s / 1 = origin + (b + s) / 1 := by
    intro s _hs
    simp only [div_one]
    ring
  let E := seedCylinderReclock e (by norm_num : (0 : ℝ) < 1) ordConnected_Icc
    (fun u : ℝ => b + u) hmem hmono hclock
  obtain ⟨G0, hread⟩ := M47Positive.exists_component_closed_ordinary_history P
    (sub_neg.mpr hab) U hne E
  have hI : Icc (origin + a) (origin + b) ⊆
      Icc ((origin + b) + (a - b)) (origin + b) := by
    intro t ht
    constructor <;> linarith only [ht.1, ht.2]
  let G : RicciFlow 3 U (Icc (origin + a) (origin + b)) := {
    metric := G0.metric
    connection := G0.connection
    interval := ordConnected_Icc
    nontrivial := ⟨origin + a, ⟨le_rfl, by linarith only [hab]⟩,
      origin + b, ⟨by linarith only [hab], le_rfl⟩, by linarith only [hab]⟩
    smooth := G0.smooth.mono (prod_mono hI Subset.rfl)
    equation := fun t ht y v w => (G0.equation t (hI ht) y v w).mono hI }
  refine ⟨G, ?_⟩
  intro s hs x
  have hsm : s - b ∈ Icc (a - b) 0 := by
    constructor <;> linarith only [hs.1, hs.2]
  have hparam : b + (s - b) = s := by ring
  have htime : (origin + b) + (s - b) / 1 = origin + s / 1 := by
    simp only [div_one]
    ring
  have hfunctions :
      (⟨(origin + b) + (s - b) / 1,
        fun y : U => E.forward (s - b) hsm y.val⟩ :
          (t : ℝ) × (U → (F.slice t).carrier)) =
        ⟨origin + s / 1, fun y : U => e.forward s hs y.val⟩ := by
    apply Sigma.ext htime
    apply Function.hfunext rfl
    intro y y' hyy
    cases hyy
    have hf := seedCylinderReclock_forward_heq e (by norm_num : (0 : ℝ) < 1)
      ordConnected_Icc (fun u : ℝ => b + u) hmem hmono hclock (s - b) hsm y.val
    have heq : ∀ t (ht : t ∈ Icc a b), t = s →
        HEq (e.forward t ht y.val) (e.forward s hs y.val) := by
      intro t ht hts
      subst t
      rfl
    exact hf.trans (heq _ _ hparam)
  refine ⟨?_, ?_, ?_⟩
  · intro v w
    have hm := congrArg (fun p : (t : ℝ) × (U → (F.slice t).carrier) =>
      (F.metric p.1).inner (p.2 x)
        (mfderiv (𝓡 3) (𝓡 3) p.2 x v) (mfderiv (𝓡 3) (𝓡 3) p.2 x w)) hfunctions
    exact hm.symm.trans (((hread (s - b) hsm x).1 v w).trans
      (congrArg (fun t => (G0.metric t).inner x v w) htime))
  · have hscalar := congrArg (fun p : (t : ℝ) × (U → (F.slice t).carrier) =>
      (F.connection p.1).scalarCurvature (p.2 x)) hfunctions
    exact (congrArg (fun t => (G0.connection t).scalarCurvature x) htime).symm.trans
      ((hread (s - b) hsm x).2.1.trans hscalar)
  · have hcurv := congrArg (fun p : (t : ℝ) × (U → (F.slice t).carrier) =>
      (F.connection p.1).curvatureTensorNorm (p.2 x)) hfunctions
    exact (congrArg (fun t => (G0.connection t).curvatureTensorNorm x) htime).symm.trans
      ((hread (s - b) hsm x).2.2.trans hcurv)

end PoincareConjecture.Proofs.M47
