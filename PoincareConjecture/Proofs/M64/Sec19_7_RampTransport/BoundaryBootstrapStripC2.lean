import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Boundary.StripSourceNeighborhood





noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric Complex
open scoped Topology ContDiff Manifold

namespace PoincareConjecture.M64.RampTransport

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "S" => Set.ofPred (fun p : LoopPlane => p 1 ∈ Icc (0 : ℝ) 1)




theorem annulus_boundary_c2_of_coordinates (f : LoopPlane → M)
    {r : ℝ} (hr : r ≠ 0) (x : ℝ) (upper : Bool)
    {R : ℝ} (hR : 0 < R)
    (hsource : MapsTo (f ∘ annulusBoundarySource r hr upper x)
      (closedBall (0 : ℂ) R ∩ {z | 0 ≤ z.im})
      (chartAt (EuclideanSpace ℝ (Fin n))
        (f (annulusPoint x (if upper then 1 else 0)))).source)
    (hC2 : ContDiffOn ℝ 2
      ((chartAt (EuclideanSpace ℝ (Fin n))
        (f (annulusPoint x (if upper then 1 else 0)))) ∘ f ∘
        annulusBoundarySource r hr upper x)
      (closedBall (0 : ℂ) R ∩ {z | 0 ≤ z.im})) :
    ContMDiffWithinAt (𝓡 2) (𝓡 n) 2 f S
      (annulusPoint x (if upper then 1 else 0)) := by
  let a := annulusPoint x (if upper then 1 else 0)
  let e := annulusBoundaryLinear r hr upper
  let P := annulusBoundarySource r hr upper x
  let Q : LoopPlane → ℂ := fun p => e.symm (p - a)
  let q := chartAt (EuclideanSpace ℝ (Fin n)) (f a)
  let K := closedBall (0 : ℂ) R ∩ {z | 0 ≤ z.im}
  let V := Q ⁻¹' closedBall (0 : ℂ) R
  have hQ : ContDiff ℝ 2 Q := e.symm.contDiff.comp (contDiff_id.sub contDiff_const)
  have hQa : Q a = 0 := by simp [Q]
  have hPQ (p : LoopPlane) : P (Q p) = p := by
    change a + e (e.symm (p - a)) = p
    rw [e.apply_symm_apply]
    abel
  have hV : V ∈ 𝓝 a := by
    apply hQ.continuous.continuousAt.preimage_mem_nhds
    rw [hQa]
    exact closedBall_mem_nhds _ hR
  have haS : a ∈ S := by cases upper <;> norm_num [a, annulusPoint, Set.mem_ofPred_eq]
  have haV : a ∈ V := by
    change Q a ∈ closedBall (0 : ℂ) R
    rw [hQa]
    exact mem_closedBall_self hR.le
  have hmap : MapsTo Q (S ∩ V) K := by
    intro p hp
    refine ⟨hp.2, ?_⟩
    change 0 ≤ (Q p).im
    have heq := congrArg (fun v : LoopPlane => v 1) (hPQ p)
    change (annulusBoundarySource r hr upper x (Q p)) 1 = p 1 at heq
    rw [annulusBoundarySource_apply] at heq
    change (if upper then 1 - (Q p).im else (Q p).im) = p 1 at heq
    cases upper
    · change (Q p).im = p 1 at heq
      rw [heq]
      exact hp.1.1
    · change 1 - (Q p).im = p 1 at heq
      linarith [hp.1.2]
  have hback : ContMDiffOn (𝓡 n) (𝓡 n) 2 q.symm q.target := contMDiffOn_chart_symm
  have hlocal : ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 n) 2 (f ∘ P) K := by
    apply (hback.comp hC2.contMDiffOn (fun z hz => q.map_source (hsource hz))).congr
    intro z hz
    exact (q.left_inv (hsource hz)).symm
  have hpull : ContMDiffOn (𝓡 2) (𝓡 n) 2 f (S ∩ V) := by
    apply (hlocal.comp hQ.contMDiff.contMDiffOn hmap).congr
    intro p _
    simp only [Function.comp_apply, hPQ]
  exact (hpull a ⟨haS, haV⟩).mono_of_mem_nhdsWithin
    (inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds hV))




theorem annulus_strip_c2_of_boundary_charts (f : LoopPlane → M)
    {r : ℝ} (hr : r ≠ 0)
    (hinterior : ContMDiffOn (𝓡 2) (𝓡 n) ∞ f m64AnnulusOpenStrip)
    (hboundary : ∀ (x : ℝ) (upper : Bool),
      let a := annulusPoint x (if upper then 1 else 0)
      let q := chartAt (EuclideanSpace ℝ (Fin n)) (f a)
      let P := annulusBoundarySource r hr upper x
      ∃ R : ℝ, 0 < R ∧ R < 1 ∧
        MapsTo (f ∘ P) (closedBall (0 : ℂ) R ∩ {z | 0 ≤ z.im}) q.source ∧
        ContDiffOn ℝ 2 (q ∘ f ∘ P) (closedBall (0 : ℂ) R ∩ {z | 0 ≤ z.im})) :
    ContMDiffOn (𝓡 2) (𝓡 n) 2 f S := by
  intro p hp
  by_cases h0 : p 1 = 0
  · have heq : p = annulusPoint (p 0) 0 := by
      ext i
      fin_cases i <;> simp [annulusPoint, h0]
    obtain ⟨R, hR, _, hsrc, hc⟩ := hboundary (p 0) false
    simpa only [Bool.false_eq_true, if_false, ← heq] using
      annulus_boundary_c2_of_coordinates f hr (p 0) false hR hsrc hc
  by_cases h1 : p 1 = 1
  · have heq : p = annulusPoint (p 0) 1 := by
      ext i
      fin_cases i <;> simp [annulusPoint, h1]
    obtain ⟨R, hR, _, hsrc, hc⟩ := hboundary (p 0) true
    simpa only [if_true, ← heq] using
      annulus_boundary_c2_of_coordinates f hr (p 0) true hR hsrc hc
  have hpopen : p ∈ m64AnnulusOpenStrip :=
    ⟨lt_of_le_of_ne hp.1 (Ne.symm h0), lt_of_le_of_ne hp.2 h1⟩
  exact ((hinterior.contMDiffAt (isOpen_m64AnnulusOpenStrip.mem_nhds hpopen)).of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contMDiffWithinAt

end PoincareConjecture.M64.RampTransport
