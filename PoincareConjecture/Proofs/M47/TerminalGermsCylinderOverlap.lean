import PoincareConjecture.Proofs.M47.SeedM15Cylinder
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Coefficients











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47



theorem terminalGerms_cylinder_transition_coefficients
    {F : SurgeryFlowData.{u}} {C D : GeneralizedSliceCarrier.{u}}
    {origin a : ℝ} {I J : Set ℝ} {U : Set C.carrier} {V : Set D.carrier}
    (e : SurgeryFlowCylinder F C origin 1 I U)
    (f : SurgeryFlowCylinder F D origin 1 J V)
    (ha : a ≤ 0) (hI : Icc a 0 ⊆ I) (hJ : Icc a 0 ⊆ J)
    {W Z : Set (EuclideanSpace ℝ (Fin 3))} (hW : IsOpen W) (hZ : IsOpen Z)
    (p : EuclideanSpace ℝ (Fin 3) → C.carrier)
    (q : EuclideanSpace ℝ (Fin 3) → D.carrier)
    (T : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (hp : ContMDiffOn (𝓡 3) (𝓡 3) ∞ p W)
    (hq : ContMDiffOn (𝓡 3) (𝓡 3) ∞ q Z)
    (hT : ContDiffOn ℝ ∞ T W)
    (hpU : MapsTo p W U) (hqV : MapsTo q Z V) (hTZ : MapsTo T W Z)
    (hterminal : ∀ x ∈ W,
      e.forward 0 (hI ⟨ha, le_rfl⟩) (p x) =
        f.forward 0 (hJ ⟨ha, le_rfl⟩) (q (T x)))
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ W)
    (v w : EuclideanSpace ℝ (Fin 3)) :
    (F.metric (origin + a / 1)).pullbackCoefficients
        (f.forward a (hJ ⟨le_rfl, ha⟩) ∘ q) (T x)
        (fderiv ℝ T x v) (fderiv ℝ T x w) =
      (F.metric (origin + a / 1)).pullbackCoefficients
        (e.forward a (hI ⟨le_rfl, ha⟩) ∘ p) x v w := by
  let P := e.forward a (hI ⟨le_rfl, ha⟩) ∘ p
  let Q := f.forward a (hJ ⟨le_rfl, ha⟩) ∘ q
  have hP : ContMDiffAt (𝓡 3) (𝓡 3) ∞ P x :=
    ((e.forward_smooth a (hI ⟨le_rfl, ha⟩)).comp hp hpU).contMDiffAt
      (hW.mem_nhds hx)
  have hQ : ContMDiffAt (𝓡 3) (𝓡 3) ∞ Q (T x) :=
    ((f.forward_smooth a (hJ ⟨le_rfl, ha⟩)).comp hq hqV).contMDiffAt
      (hZ.mem_nhds (hTZ hx))
  have hTx : ContDiffAt ℝ ∞ T x := (hT x hx).contDiffAt (hW.mem_nhds hx)
  have heq : Q ∘ T =ᶠ[𝓝 x] P := by
    filter_upwards [hW.mem_nhds hx] with y hy
    exact (seedM15_cylinder_eq_of_terminal e f ha hI hJ (p y) (hpU hy)
      (q (T y)) (hqV (hTZ hy)) (hterminal y hy)).symm
  have hd := mfderiv_comp x (hQ.mdifferentiableAt (by simp))
    (hTx.differentiableAt (by simp)).mdifferentiableAt
  rw [heq.mfderiv_eq, mfderiv_eq_fderiv] at hd
  change (F.metric _).inner (Q (T x))
      (mfderiv (𝓡 3) (𝓡 3) Q (T x) (fderiv ℝ T x v))
      (mfderiv (𝓡 3) (𝓡 3) Q (T x) (fderiv ℝ T x w)) =
    (F.metric _).inner (P x)
      (mfderiv (𝓡 3) (𝓡 3) P x v) (mfderiv (𝓡 3) (𝓡 3) P x w)
  have hv := congrArg (fun A => A v) hd
  have hw := congrArg (fun A => A w) hd
  have hbase := congrArg (fun z => (F.metric (origin + a / 1)).inner z
    (mfderiv (𝓡 3) (𝓡 3) Q (T x) (fderiv ℝ T x v))
    (mfderiv (𝓡 3) (𝓡 3) Q (T x) (fderiv ℝ T x w))) heq.self_of_nhds
  exact hbase.trans (congrArg₂ (fun b c : EuclideanSpace ℝ (Fin 3) =>
    (F.metric (origin + a / 1)).inner (P x) b c) hv.symm hw.symm)

end PoincareConjecture.M47
