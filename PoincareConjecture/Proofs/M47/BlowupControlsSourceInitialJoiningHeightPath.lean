import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialJoiningHeight
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Measure.HausdorffDensity.LocalDistance

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal NNReal

universe u

namespace PoincareConjecture.M47

open Proofs.M46

theorem source_initial_joining_height_path_length
    {F : SurgeryFlowData.{u}} {t : ℝ} {hT : t ∈ F.surgery_times}
    [Nonempty (F.slice t).carrier] {i : Fin (F.event t hT).cap_count}
    {S : MaximalStandardCapFlow F.standard_initial} {A eta Lambda : ℝ}
    {J : Set ℝ} {V : Set (F.slice t).carrier}
    (e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) J V)
    (initial : SurgeryCapInitialComparison F t hT i A)
    (comparison : SurgeryCapFamilyComparison F S A eta e initial.chart)
    (hzero : (0 : ℝ) ∈ J) (hbase : ∀ y ∈ V, HEq (e.forward 0 hzero y) y)
    (heta : 0 < eta) (hetaSmall : eta ≤ 1 / 1000) (hLambda : 0 < Lambda)
    (hbudget : 1 ≤ (1 - ((F.event t hT).necks i).neck.epsilon) * Lambda ^ 2)
    {U : Set StandardCapSpace} (hU : IsOpen U)
    (hsource : U ⊆ F.standard_initial.metric.ball 0 A)
    (havoid : ∀ x ∈ U, initial.chart x ∉ ((F.event t hT).caps i).carrier)
    {p : ℝ → StandardCapSpace}
    (hp : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 p (Icc 0 1))
    (himage : MapsTo p (Icc (0 : ℝ) 1) U) :
    edist
        (((((F.event t hT).necks i).neck.coordinate_inverse
          (sourceInitialOldMap initial (p 0))).2))
        (((((F.event t hT).necks i).neck.coordinate_inverse
          (sourceInitialOldMap initial (p 1))).2)) ≤
      ENNReal.ofReal ((101 / 100 : ℝ) * Lambda) *
        F.standard_initial.metric.pathELength p 0 1 := by
  let old := ((F.event t hT).necks i).neck
  let f : StandardCapSpace → ℝ := fun z => (old.coordinate_inverse
    (sourceInitialOldMap initial z)).2
  have hf (z : StandardCapSpace) (hz : z ∈ U) :
      ContMDiffAt (𝓡 3) (𝓘(ℝ, ℝ)) 1 f z := by
    obtain ⟨hmap, _, hnegative⟩ := source_initial_old_map_properties initial hsource havoid
    have hzf := hnegative hz
    have hcoord := old.coordinate_inverse_smooth (sourceInitialOldMap initial z) hzf.1
    have hfmap := (hmap z hz).contMDiffAt (hU.mem_nhds hz)
    exact ((hcoord.contMDiffAt (old.carrier_open.mem_nhds hzf.1)).snd.comp z
      hfmap).of_le (by simp)
  let : Bundle.RiemannianBundle
      (TangentSpace (𝓡 3) : StandardCapSpace → Type _) :=
    ⟨F.standard_initial.metric.toRiemannianMetric⟩
  have hnorm (z : StandardCapSpace) (w : TangentSpace (𝓡 3) z) :
      ‖w‖ = F.standard_initial.metric.tangentNorm z w := by
    rw [norm_eq_sqrt_real_inner]
    rfl
  let K : ℝ≥0 := Real.toNNReal ((101 / 100 : ℝ) * Lambda)
  have hK (z : StandardCapSpace) (hz : z ∈ U) :
      ‖mvfderiv (𝓡 3) f z‖ₑ ≤
        ENNReal.ofReal ((101 / 100 : ℝ) * Lambda) := by
    apply ContinuousLinearMap.opENorm_le_bound
    intro w
    have hder := source_initial_joining_height_derivative e initial comparison hzero hbase
      heta hetaSmall hLambda hbudget hU hsource havoid hz w
    have hb := ENNReal.ofReal_le_ofReal hder
    rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (101 / 100 : ℝ) * Lambda)] at hb
    simpa only [← ofReal_norm, hnorm, Real.norm_eq_abs] using hb
  exact Poincare.edist_le_mul_pathELength_of_mfderiv_le
    (M := StandardCapSpace) (E := EuclideanSpace ℝ (Fin 3)) (F := ℝ)
    (I := 𝓡 3) (s := U) (f := f) (K := K)
    hf (fun z hz => by exact hK z hz) hp himage

end PoincareConjecture.M47
