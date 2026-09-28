import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.EndBall.TerminalCylinder



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

open Poincare.Geometry.Euclidean

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1
local notation "IP" => ModelWithCorners.prod (𝓡 1) 𝓘(Real, Real)



theorem exists_model_cylindrical_preparation
    {v : E3} (hv : ‖v‖ = 1) {f : S2 → E3}
    (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    (d : OpenPartialHomeomorph E2 S2) (T : OpenPartialHomeomorph (S1 × Real) S2)
    (hT : ContMDiffOn IP (𝓡 2) ∞ T T.source)
    (hTi : ContMDiffOn (𝓡 2) IP ∞ T.symm T.target)
    {b ε R : Real} (hε : 0 < ε) (hR : 0 < R)
    (hsource : univ ×ˢ Icc (b - ε) (b + ε) ⊆ T.source)
    (hphysical : ∀ q t, t ∈ Icc (b - ε) (b + ε) → inner Real v (f (T (q, t))) = t)
    (hboundary : range (fun q : S1 => T (q, b)) = d '' sphere (0 : E2) 1)
    (hinside : ∀ q t, t ∈ Ioo (b - ε) b → T (q, t) ∈ d '' ball (0 : E2) 1) :
    ∃ r : Real, 0 < r ∧ r < R ∧
      ∃ G : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      ∃ C : OpenPartialHomeomorph (S1 × Real) S2,
        (∀ x, inner Real v (G x) = inner Real v x) ∧
        (∃ K : Set E3, IsCompact K ∧ K ⊆ {x | |inner Real v x - b| ≤ R} ∧
          ∀ x ∉ K, G x = x) ∧
        EqOn G id {x | inner Real v x = b} ∧
        C.source = univ ×ˢ Ioo (-r) r ∧
        (∀ q t, t ∈ Ioo (-r) r →
          G (f (C (q, t))) = (b + t) • v +
            ((Hemisphere.Plane v).orthogonalProjectionOnto (f (T (q, b))) : E3)) ∧
        range (fun q : S1 => C (q, 0)) = d '' sphere (0 : E2) 1 ∧
        (∀ q t, t ∈ Ioo (-r) 0 → C (q, t) ∈ d '' ball (0 : E2) 1) ∧
        ∀ q t, C (q, t) = T (q, b + t) := by
  have hbase (q : S1) : (q, b) ∈ T.source :=
    hsource ⟨mem_univ _, by linarith, by linarith⟩
  have hinj : Injective (fun z : PUnit.{1} × S1 => T (z.2, b)) := by
    intro z z' heq
    exact Prod.ext (Subsingleton.elim _ _)
      (congrArg Prod.fst (T.injOn (hbase z.2) (hbase z'.2) heq))
  obtain ⟨r₀, hr₀, hr₀R, G, hGheight, hsupport, hcentral, hmotion⟩ :=
    Saddle.Caps.exists_terminal_cylinder_straightening hv hf
      (fun _ : PUnit.{1} => T) (fun _ => hT) (fun _ => hTi) b
      (fun _ => ⟨ε, hε, hsource, hphysical⟩) hinj hR
  let r := min r₀ ε
  have hr : 0 < r := lt_min hr₀ hε
  have hrr : r ≤ r₀ := min_le_left _ _
  have hre : r ≤ ε := min_le_right _ _
  let A : (S1 × Real) ≃ₜ (S1 × Real) :=
    (Homeomorph.refl S1).prodCongr (Homeomorph.addRight b)
  let U := A.toOpenPartialHomeomorph.trans T
  let C := U.restrOpen (univ ×ˢ Ioo (-r) r) (isOpen_univ.prod isOpen_Ioo)
  have hC (q : S1) (t : Real) : C (q, t) = T (q, b + t) := by
    change T (q, t + b) = _
    rw [add_comm t b]
  have hUs : univ ×ˢ Ioo (-r) r ⊆ U.source := by
    rintro ⟨q, t⟩ ⟨_, ht⟩
    refine ⟨mem_univ _, ?_⟩
    change (q, t + b) ∈ T.source
    apply hsource
    exact ⟨mem_univ _, by linarith [ht.1], by linarith [ht.2]⟩
  refine ⟨r, hr, hrr.trans_lt hr₀R, G, C, hGheight, hsupport, hcentral,
    inter_eq_right.mpr hUs, ?_, ?_, ?_, hC⟩
  · intro q t ht
    rw [hC, hmotion PUnit.unit t ⟨by linarith [ht.1], by linarith [ht.2]⟩ q]
    have hh := (heightCoordinates hv).apply_symm_apply (f (T (q, b)))
    change inner Real v (f (T (q, b))) • v +
      ((Hemisphere.Plane v).orthogonalProjectionOnto (f (T (q, b))) : E3) = _ at hh
    rw [hphysical q b ⟨by linarith, by linarith⟩] at hh
    nth_rw 1 [← hh]
    rw [add_smul]
    abel
  · simpa only [hC, add_zero] using hboundary
  · intro q t ht
    rw [hC]
    exact hinside q (b + t) ⟨by linarith [ht.1], by linarith [ht.2]⟩

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing
