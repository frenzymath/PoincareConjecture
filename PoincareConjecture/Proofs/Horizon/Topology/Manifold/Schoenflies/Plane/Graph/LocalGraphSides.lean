import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Graph.LocalTwoSides
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith











set_option autoImplicit false

open Set Metric Topology

namespace Poincare.Manifold.Schoenflies.Plane



def graphFlatteningHomeomorph {T G : Type*} [TopologicalSpace T]
    [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    (g : T → G) (hg : Continuous g) : (T × G) ≃ₜ (T × G) where
  toFun p := (p.1, p.2 - g p.1)
  invFun p := (p.1, p.2 + g p.1)
  left_inv p := by simp
  right_inv p := by simp
  continuous_toFun := continuous_fst.prodMk (continuous_snd.fun_sub (hg.comp continuous_fst))
  continuous_invFun := continuous_fst.prodMk (continuous_snd.fun_add (hg.comp continuous_fst))

variable {X : Type*} [TopologicalSpace X] {C : Set X}



theorem hasLocalTwoSides_of_local_straightening
    (hchart : ∀ q ∈ C, ∃ e : X ≃ₜ (ℝ × ℝ), ∃ U : Set X,
      IsOpen U ∧ q ∈ U ∧ ∀ z ∈ U, z ∈ C ↔ (e z).2 = 0) : HasLocalTwoSides C := by
  intro q hq
  obtain ⟨e, U, hU, hqU, heC⟩ := hchart q hq
  have hqzero : (e q).2 = 0 := (heC q hqU).mp hq
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp (e.isOpenMap U hU) (e q)
    (mem_image_of_mem e hqU)
  let a := (e q).1
  let R : Set (ℝ × ℝ) := Ioo (a - r) (a + r) ×ˢ Ioo (-r) r
  let A0 : Set (ℝ × ℝ) := Ioo (a - r) (a + r) ×ˢ Ioo (-r) 0
  let B0 : Set (ℝ × ℝ) := Ioo (a - r) (a + r) ×ˢ Ioo 0 r
  have hRball : R = ball (e q) r := by
    have heq : e q = (a, 0) := Prod.ext rfl hqzero
    rw [heq, ← ball_prod_same, Real.ball_eq_Ioo, Real.ball_zero_eq_Ioo]
  have hWU : e ⁻¹' R ⊆ U := by
    intro z hz
    have him : e z ∈ e '' U := hrU (hRball ▸ hz)
    obtain ⟨w, hw, hew⟩ := him
    exact e.injective hew ▸ hw
  have har : a - r < a + r := by linarith
  have hAr : A0 ⊆ R := fun z hz => ⟨hz.1, hz.2.1, hz.2.2.trans hr⟩
  have hBr : B0 ⊆ R := fun z hz => ⟨hz.1, (neg_neg_of_pos hr).trans hz.2.1, hz.2.2⟩
  refine ⟨e ⁻¹' R, e ⁻¹' A0, e ⁻¹' B0,
    (isOpen_Ioo.prod isOpen_Ioo).preimage e.continuous, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change e q ∈ R
    rw [hRball]
    exact mem_ball_self hr
  · exact e.isConnected_preimage.mpr
      ((isConnected_Ioo har).prod (isConnected_Ioo (neg_neg_of_pos hr)))
  · exact e.isConnected_preimage.mpr ((isConnected_Ioo har).prod (isConnected_Ioo hr))
  · apply subset_antisymm
    · rintro z (hz | hz)
      · refine ⟨hAr hz, ?_⟩
        intro hzC
        exact hz.2.2.ne ((heC z (hWU (hAr hz))).mp hzC)
      · refine ⟨hBr hz, ?_⟩
        intro hzC
        exact hz.2.1.ne' ((heC z (hWU (hBr hz))).mp hzC)
    · rintro z ⟨hz, hzC⟩
      have hz0 : (e z).2 ≠ 0 := fun hez => hzC ((heC z (hWU hz)).mpr hez)
      rcases hz0.lt_or_gt with hneg | hpos
      · exact Or.inl ⟨hz.1, hz.2.1, hneg⟩
      · exact Or.inr ⟨hz.1, hpos, hz.2.2⟩
  · rintro z ⟨hzC, hzR⟩
    rw [← e.preimage_closure]
    change e z ∈ closure A0
    rw [closure_prod_eq, closure_Ioo har.ne, closure_Ioo (neg_neg_of_pos hr).ne]
    exact ⟨⟨hzR.1.1.le, hzR.1.2.le⟩, by
      rw [(heC z (hWU hzR)).mp hzC]
      exact ⟨(neg_neg_of_pos hr).le, le_rfl⟩⟩
  · rintro z ⟨hzC, hzR⟩
    rw [← e.preimage_closure]
    change e z ∈ closure B0
    rw [closure_prod_eq, closure_Ioo har.ne, closure_Ioo hr.ne]
    exact ⟨⟨hzR.1.1.le, hzR.1.2.le⟩, by
      rw [(heC z (hWU hzR)).mp hzC]
      exact ⟨le_rfl, hr.le⟩⟩



theorem hasLocalTwoSides_of_local_graph
    (hchart : ∀ q ∈ C, ∃ e : X ≃ₜ (ℝ × ℝ), ∃ g : ℝ → ℝ, Continuous g ∧
      ∃ U : Set X, IsOpen U ∧ q ∈ U ∧ ∀ z ∈ U, z ∈ C ↔ (e z).2 = g (e z).1) :
    HasLocalTwoSides C := by
  apply hasLocalTwoSides_of_local_straightening
  intro q hq
  obtain ⟨e, g, hg, U, hU, hqU, heC⟩ := hchart q hq
  refine ⟨e.trans (graphFlatteningHomeomorph g hg), U, hU, hqU, ?_⟩
  intro z hz
  change z ∈ C ↔ (e z).2 - g (e z).1 = 0
  rw [sub_eq_zero]
  exact heC z hz

end Poincare.Manifold.Schoenflies.Plane
