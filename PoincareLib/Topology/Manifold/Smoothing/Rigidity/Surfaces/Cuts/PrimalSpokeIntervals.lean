import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.Cuts.PrimalDiskSpokes
import PoincareLib.Topology.Manifold.Smoothing.Dehn.Arcs.Mathlib.JoinedPLIntervals

/-!
# Exact simultaneous spoke intervals

The common cone chart gives interval images with exact singleton contacts.
Joining two such spokes gives the embedded return interval through the center.
-/

set_option autoImplicit false

open Set Geometry

namespace PoincareMT.M76.OriginalTriangleCopies

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_primal_spoke_intervals {d q : Set E}
    (hd : IsFinitePLBallPair (ℝ × ℝ) d q) (x₀ : q) :
    ∃ center ∈ d \ q, ∃ arcs : q → Set E,
      (∀ x, IsFinitePLBallPair ℝ (arcs x) {center, (x : E)}) ∧
      (∀ x, arcs x ⊆ d) ∧
      (∀ x, arcs x ∩ q = {(x : E)}) ∧
      (∀ x y, x ≠ y → arcs x ∩ arcs y = {center}) := by
  obtain ⟨c, hc, f, hf, hfd, hends, hfibers, hfrim⟩ := exists_primal_disk_spokes hd x₀
  let arcs : q → Set E := fun x ↦ f x '' Icc (0 : ℝ) 1
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have hone : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  refine ⟨c, hc, arcs, ?_, ?_, ?_, ?_⟩
  · intro x
    have hinj : InjOn (f x) (Icc (0 : ℝ) 1) := by
      intro u hu v hv huv
      exact ((hfibers x x u v hu hv).mp huv).1
    simpa only [image_pair, (hends x).1, (hends x).2] using
      (isFinitePLBallPair_Icc (show (0 : ℝ) < 1 by norm_num)).image (hf x) hinj
  · rintro x z ⟨t, ht, rfl⟩
    exact hfd x t ht
  · intro x
    ext z
    constructor
    · rintro ⟨⟨t, ht, rfl⟩, hq⟩
      rw [(hfrim x t ht).mp hq, (hends x).2]
      rfl
    · rintro rfl
      exact ⟨⟨1, hone, (hends x).2⟩, x.property⟩
  · intro x y hxy
    ext z
    constructor
    · rintro ⟨⟨u, hu, rfl⟩, ⟨v, hv, heq⟩⟩
      have h := (hfibers x y u v hu hv).mp heq.symm
      have hu0 : u = 0 := h.2.resolve_right hxy
      rw [hu0, (hends x).1]
      rfl
    · rintro rfl
      exact ⟨⟨0, hzero, (hends x).1⟩, ⟨0, hzero, (hends y).1⟩⟩

/-- The two spoke intervals join at their common center with their original
rim endpoints as the complete boundary of the return interval. -/
theorem joined_spokes_isFinitePLInterval {A B : Set E} {c a b : E}
    (hA : IsFinitePLBallPair ℝ A {c, a})
    (hB : IsFinitePLBallPair ℝ B {c, b})
    (hca : c ≠ a) (hcb : c ≠ b) (hAB : A ∩ B = {c}) :
    IsFinitePLBallPair ℝ (A ∪ B) {a, b} := by
  have hA' : IsFinitePLBallPair ℝ A {a, c} := by
    simpa only [Set.pair_comm] using hA
  obtain ⟨p, hp, hp0, hp1⟩ := hA'.exists_unitInterval_chart_with_endpoints hca.symm
  obtain ⟨r, hr, hr0, hr1⟩ := hB.exists_unitInterval_chart_with_endpoints hcb
  exact Dehn.isFinitePLBallPair_joined_intervals p r hp hr hp0 hp1 hr0 hr1 hAB

end PoincareMT.M76.OriginalTriangleCopies
