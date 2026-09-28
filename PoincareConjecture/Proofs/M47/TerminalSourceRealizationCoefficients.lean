import PoincareConjecture.Proofs.M47.TerminalSourceRealization
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_CoefficientTransport










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)



theorem terminalSourceRealization_terminal_metric
    {S : SurgeryFlowData.{u}} {b Q : ℝ} {I J : Set ℝ}
    (U : TopologicalSpace.Opens (S.slice b).carrier)
    (e : SurgeryFlowCylinder S (S.slice b) b Q I U) (hzero : (0 : ℝ) ∈ I)
    (hbased : ∀ hs x, x ∈ U → HEq (e.forward 0 hs x) x)
    (F : RicciFlow 3 U J)
    (hmetric : ∀ (x : U) (v w : TangentSpace (𝓡 3) x),
      (F.metric 0).inner x v w = e.pullbackInner 0 hzero x.val
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → (S.slice b).carrier) x v)
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → (S.slice b).carrier) x w))
    (x : U) (v w : TangentSpace (𝓡 3) x) :
    (F.metric 0).inner x v w = Q * (S.metric b).inner x.val
      (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → (S.slice b).carrier) x v)
      (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → (S.slice b).carrier) x w) := by
  have hfunctions :
      (⟨b + 0 / Q, fun y : U => e.forward 0 hzero y.val⟩ :
        (t : ℝ) × (U → (S.slice t).carrier)) =
        ⟨b, (Subtype.val : U → (S.slice b).carrier)⟩ := by
    apply Sigma.ext (by simp only [zero_div, add_zero])
    apply Function.hfunext rfl
    intro y y' hyy
    cases hyy
    exact hbased _ y.val y.property
  have hpull := congrArg (fun p : (t : ℝ) × (U → (S.slice t).carrier) =>
    (S.metric p.1).inner (p.2 x)
      (mfderiv (𝓡 3) (𝓡 3) p.2 x v) (mfderiv (𝓡 3) (𝓡 3) p.2 x w)) hfunctions
  have hf := (e.forward_smooth 0 hzero x.val x.property).contMDiffAt
    (U.isOpen.mem_nhds x.property)
  have hd := mfderiv_comp x (hf.mdifferentiableAt (by simp))
    (contMDiff_subtype_val (n := ∞) x |>.mdifferentiableAt (by simp))
  change mfderiv (𝓡 3) (𝓡 3) (fun y : U => e.forward 0 hzero y.val) x = _ at hd
  rw [hd] at hpull
  exact (hmetric x v w).trans (congrArg (fun z : ℝ => Q * z) hpull)




theorem terminalSourceRealization_pullbackCoefficients
    {C : GeneralizedSliceCarrier.{u}} (S : ℝ → GeneralizedSliceCarrier.{u})
    (g : ∀ t : ℝ, RiemannianMetric 3 (S t).carrier)
    {b Q τ : ℝ} (hQ : 0 < Q) (U : TopologicalSpace.Opens C.carrier)
    (A : ∀ s : ℝ, s ∈ Icc (-τ) 0 → C.carrier → (S (b + s / Q)).carrier)
    (hA : ∀ s hs, ContMDiffOn (𝓡 3) (𝓡 3) ∞ (A s hs) U)
    (F : RicciFlow 3 U (Icc (-τ) 0))
    (hmetric : ∀ (s : ℝ) (hs : s ∈ Icc (-τ) 0) (y : U)
      (v w : TangentSpace (𝓡 3) y),
      (F.metric s).inner y v w = Q * (g (b + s / Q)).inner (A s hs y.val)
        (mfderiv (𝓡 3) (𝓡 3) (A s hs) y.val
          (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) y v))
        (mfderiv (𝓡 3) (𝓡 3) (A s hs) y.val
          (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) y w)))
    {V : Set E} (hV : IsOpen V) (Phi : E → U)
    (hPhi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ Phi V) :
    ∀ (s : ℝ) (hs : s ∈ Icc (-τ) 0) (x : E), x ∈ V →
      ((F.metric s).pullbackCoefficients Phi x =
        Q • (g (b + s / Q)).pullbackCoefficients (fun z => A s hs (Phi z).val) x) ∧
      ∀ v w : E, (F.metric s).pullbackCoefficients Phi x v w =
        Q * (g (b + s / Q)).inner (A s hs (Phi x).val)
          (mfderiv (𝓡 3) (𝓡 3) (A s hs) (Phi x).val
            (mfderiv (𝓡 3) (𝓡 3) (fun z => (Phi z).val) x v))
          (mfderiv (𝓡 3) (𝓡 3) (A s hs) (Phi x).val
            (mfderiv (𝓡 3) (𝓡 3) (fun z => (Phi z).val) x w)) := by
  intro s hs x hx
  have hf := (hA s hs (Phi x).val (Phi x).property).contMDiffAt
    (U.isOpen.mem_nhds (Phi x).property)
  have hi : ContMDiffAt (𝓡 3) (𝓡 3) ∞ (Subtype.val : U → C.carrier) (Phi x) :=
    contMDiff_subtype_val (n := ∞) (Phi x)
  have hp := (hPhi x hx).contMDiffAt (hV.mem_nhds hx)
  have hd := mfderiv_comp (Phi x) (hf.mdifferentiableAt (by simp))
    (hi.mdifferentiableAt (by simp))
  change mfderiv (𝓡 3) (𝓡 3) (fun y : U => A s hs y.val) (Phi x) = _ at hd
  constructor
  · have h := M44.pullbackCoefficients_eq_of_metric_germ (F.metric s)
      (M13.scaleSmoothMetric (g (b + s / Q)) Q hQ)
      ((hf.comp (Phi x) hi).mdifferentiableAt (by simp))
      (hp.mdifferentiableAt (by simp)) (Filter.EventuallyEq.refl _ _) (by
        intro v w
        change Q * (g (b + s / Q)).inner (A s hs (Phi x).val)
          (mfderiv (𝓡 3) (𝓡 3) (fun y : U => A s hs y.val) (Phi x) v)
          (mfderiv (𝓡 3) (𝓡 3) (fun y : U => A s hs y.val) (Phi x) w) = _
        rw [hd]
        exact (hmetric s hs (Phi x) v w).symm)
    refine h.symm.trans ?_
    ext v w
    rfl
  · intro v w
    have hpull := hmetric s hs (Phi x)
      (mfderiv (𝓡 3) (𝓡 3) Phi x v) (mfderiv (𝓡 3) (𝓡 3) Phi x w)
    have hdi := mfderiv_comp x (hi.mdifferentiableAt (by simp))
      (hp.mdifferentiableAt (by simp))
    change mfderiv (𝓡 3) (𝓡 3) (fun z => (Phi z).val) x = _ at hdi
    rw [hdi]
    exact hpull

end PoincareConjecture.M47
