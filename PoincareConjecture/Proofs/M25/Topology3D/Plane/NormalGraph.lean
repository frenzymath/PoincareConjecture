import PoincareConjecture.Proofs.M25.Topology3D.Plane.TubeCoordinates
import Mathlib.Geometry.Manifold.Algebra.SMul











set_option autoImplicit false

open Set Metric Function
open scoped Manifold ContDiff

namespace PoincareConjecture.M25.Topology3D



theorem curveAnnularTube_smooth_normal_graph
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fact (Module.finrank ℝ E = 2)]
    (o : Orientation ℝ E (Fin 2)) (q0 : sphere (0 : E) 1)
    (c : ℝ → sphere (0 : E) 1 → E)
    (T : OpenPartialHomeomorph (ℝ × E) (ℝ × E))
    {l u w : ℝ} (hw : w < 1)
    (hs : T.source = Ioo l u ×ˢ {x : E | |‖x‖ - 1| < w})
    (he : ∀ p : ℝ × E, T p = (p.1, curveAnnularExtension o q0 c p))
    (hfwd : ContDiffOn ℝ ∞ T T.source) (hInv : ContDiffOn ℝ ∞ T.symm T.target)
    (g : ℝ × sphere (0 : E) 1 → ℝ)
    (hg : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, ℝ) ∞ g)
    (hbound : ∀ z ∈ Ioo l u, ∀ q : sphere (0 : E) 1, |g (z, q)| < w) :
    let G : ℝ × sphere (0 : E) 1 → E := fun p => c p.1 p.2 + g p •
      curveFamilyNormal o (radialFamilyExtension q0 c) (p.1, (p.2 : E))
    ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, E) ∞ G (Ioo l u ×ˢ univ) ∧
      ∀ z ∈ Ioo l u, Injective (fun q => G (z, q)) ∧
        ∀ q : sphere (0 : E) 1,
          Injective (mfderiv (𝓡 1) 𝓘(ℝ, E) (fun p => G (z, p)) q) := by
  let G : ℝ × sphere (0 : E) 1 → E := fun p => c p.1 p.2 + g p •
    curveFamilyNormal o (radialFamilyExtension q0 c) (p.1, (p.2 : E))
  change ContMDiffOn _ _ ∞ G _ ∧ _
  let U : Set (ℝ × sphere (0 : E) 1) := Ioo l u ×ˢ univ
  let R : ℝ × sphere (0 : E) 1 → ℝ × E := fun p => (p.1, (1 + g p) • (p.2 : E))
  have hR : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, ℝ × E) ∞ R :=
    contMDiff_fst.prodMk_space ((contMDiff_const.add hg).smul
      ((contMDiff_coe_sphere (n := 1) (m := ∞)).comp contMDiff_snd))
  have hpos : ∀ p ∈ U, 0 < 1 + g p := by
    intro p hp
    have hb := (abs_lt.mp (hbound p.1 hp.1 p.2)).1
    linarith
  have hsource : MapsTo R U T.source := by
    intro p hp
    rw [hs]
    refine ⟨hp.1, ?_⟩
    change |‖(1 + g p) • (p.2 : E)‖ - 1| < w
    simpa [norm_smul, Real.norm_eq_abs, abs_of_pos (hpos p hp),
      norm_eq_of_mem_sphere p.2] using hbound p.1 hp.1 p.2
  have hG : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, E) ∞ G U := by
    apply ((hfwd.snd.contMDiffOn).comp hR.contMDiffOn hsource).congr
    intro p hp
    change G p = (T (R p)).2
    rw [he]
    exact (curveAnnularExtension_apply_radial o q0 c p.1 p.2
      (r := g p) (by linarith [hpos p hp])).symm
  have hcoord : ∀ z ∈ Ioo l u, ∀ q : sphere (0 : E) 1,
      (z, G (z, q)) ∈ T.target ∧ curveTubeProjection q0 T (z, G (z, q)) = q := by
    intro z hz q
    have h := curveAnnularTube_coordinates_apply o q0 c T hw hs he z hz q (hbound z hz q)
    exact ⟨h.1, h.2.1⟩
  have hx : ∀ y ∈ T.target, (T.symm y).2 ≠ 0 :=
    fun y hy => (curveAnnularTube_coordinates o q0 c T hw hs he hy).1
  have hP := contMDiffOn_curveTubeProjection (n := 1) q0 T hInv hx
  refine ⟨hG, ?_⟩
  intro z hz
  let F : sphere (0 : E) 1 → E := fun q => G (z, q)
  let P : E → sphere (0 : E) 1 := fun y => curveTubeProjection q0 T (z, y)
  have hleft : P ∘ F = id := funext (fun q => (hcoord z hz q).2)
  refine ⟨fun q1 q2 h => ?_, ?_⟩
  · exact ((hcoord z hz q1).2).symm.trans
      ((congrArg P h).trans (hcoord z hz q2).2)
  · intro q
    have hFq : ContMDiffAt (𝓡 1) 𝓘(ℝ, E) ∞ F q :=
      (hG.contMDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨hz, mem_univ q⟩)).comp q
        (contMDiffAt_const.prodMk contMDiffAt_id)
    have hPq : ContMDiffAt 𝓘(ℝ, E) (𝓡 1) ∞ P (F q) :=
      (hP.contMDiffAt (T.open_target.mem_nhds (hcoord z hz q).1)).comp (F q)
        (contMDiffAt_const.prodMk_space contMDiffAt_id)
    have hderiv := mfderiv_comp q (hPq.mdifferentiableAt (by simp))
      (hFq.mdifferentiableAt (by simp))
    rw [hleft, mfderiv_id] at hderiv
    intro v1 v2 hv
    have hv' := congrArg (mfderiv 𝓘(ℝ, E) (𝓡 1) P (F q)) hv
    change ((mfderiv 𝓘(ℝ, E) (𝓡 1) P (F q)).comp
      (mfderiv (𝓡 1) 𝓘(ℝ, E) F q)) v1 =
      ((mfderiv 𝓘(ℝ, E) (𝓡 1) P (F q)).comp
        (mfderiv (𝓡 1) 𝓘(ℝ, E) F q)) v2 at hv'
    rw [← hderiv] at hv'
    exact hv'

end PoincareConjecture.M25.Topology3D
