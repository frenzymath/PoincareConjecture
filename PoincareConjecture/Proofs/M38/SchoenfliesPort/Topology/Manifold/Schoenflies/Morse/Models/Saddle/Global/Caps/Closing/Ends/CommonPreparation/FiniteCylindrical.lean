import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Ends.CommonPreparation.Cylindrical







open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.PoincareConjecture

namespace M38Schoenflies



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

open Poincare.Geometry.Euclidean

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1
local notation "IP" => ModelWithCorners.prod (𝓡 1) 𝓘(Real, Real)

private theorem exists_uniform_positive_lt {ι : Type*} [Finite ι]
    (ε : ι → Real) (hε : ∀ i, 0 < ε i) : ∃ r : Real, 0 < r ∧ ∀ i, r < ε i := by
  have hnear : ∀ᶠ r in 𝓝 (0 : Real), ∀ i, r < ε i :=
    eventually_all.mpr (fun i => gt_mem_nhds (hε i))
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨r / 2, half_pos hr, hsub ?_⟩
  rw [mem_ball, Real.dist_eq, sub_zero, abs_of_pos (half_pos hr)]
  linarith




theorem exists_finite_common_cylindrical_preparation_of_surface_germs
    {ι : Type*} [Finite ι] {v : E3} (hv : ‖v‖ = 1) {s t : S2 → E3}
    (hs : Topology.IsEmbedding s)
    (ht : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ t)
    (d : ι → OpenPartialHomeomorph E2 S2)
    (A B : ι → OpenPartialHomeomorph (S1 × Real) S2)
    (hB : ∀ i, ContMDiffOn IP (𝓡 2) ∞ (B i) (B i).source)
    (hBi : ∀ i, ContMDiffOn (𝓡 2) IP ∞ (B i).symm (B i).target)
    (b : Real) (ε : ι → Real) (hε : ∀ i, 0 < ε i) {R : Real} (hR : 0 < R)
    (hAs : ∀ i, univ ×ˢ Icc (b - ε i) (b + ε i) ⊆ (A i).source)
    (hBs : ∀ i, univ ×ˢ Icc (b - ε i) (b + ε i) ⊆ (B i).source)
    (hAh : ∀ i q z, z ∈ Icc (b - ε i) (b + ε i) → inner Real v (s (A i (q, z))) = z)
    (hBh : ∀ i q z, z ∈ Icc (b - ε i) (b + ε i) → inner Real v (t (B i (q, z))) = z)
    (hboundary : ∀ i, range (fun q : S1 => B i (q, b)) = d i '' sphere (0 : E2) 1)
    (hinside : ∀ i q z, z ∈ Ioo (b - ε i) b → B i (q, z) ∈ d i '' ball (0 : E2) 1)
    (hinj : Injective (fun z : ι × S1 => B z.1 (z.2, b)))
    (hrim : ∀ i, range (fun q : S1 => s (A i (q, b))) =
      range (fun q : S1 => t (B i (q, b))))
    (U : ι → Set E3) (hU : ∀ i, IsOpen (U i))
    (hrimU : ∀ i, range (fun q : S1 => s (A i (q, b))) ⊆ U i)
    (hgerm : ∀ i, range s ∩ U i = range t ∩ U i) :
    ∃ r δ : Real, 0 < r ∧ r < R ∧ 0 < δ ∧ δ < r ∧ (∀ i, r < ε i) ∧
      ∃ Q : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      ∃ C : ι → OpenPartialHomeomorph (S1 × Real) S2,
        (∀ x, inner Real v (Q x) = inner Real v x) ∧
        (∃ K : Set E3, IsCompact K ∧ K ⊆ {x | |inner Real v x - b| ≤ R} ∧
          ∀ x ∉ K, Q x = x) ∧
        EqOn Q id {x | inner Real v x = b} ∧
        (∀ i, (C i).source = univ ×ˢ Ioo (-r) r) ∧
        (∀ i q z, C i (q, z) = B i (q, b + z)) ∧
        (∀ i q z, z ∈ Ioo (-r) r →
          Q (t (C i (q, z))) = (b + z) • v +
            ((Hemisphere.Plane v).orthogonalProjectionOnto (t (B i (q, b))) : E3)) ∧
        (∀ i, range (fun q : S1 => C i (q, 0)) = d i '' sphere (0 : E2) 1) ∧
        (∀ i q z, z ∈ Ioo (-r) 0 → C i (q, z) ∈ d i '' ball (0 : E2) 1) ∧
        ∀ i z, z ∈ Icc (b - δ) (b + δ) →
          range (fun q : S1 => (Hemisphere.Plane v).orthogonalProjectionOnto
            (Q (s (A i (q, z))))) =
          range (fun q : S1 => (Hemisphere.Plane v).orthogonalProjectionOnto
            (s (A i (q, b)))) := by
  classical
  choose η hη hηε hslices using fun i => exists_equal_physical_slices_of_surface_germ
    hs ht.isEmbedding (A i) (B i) (inner Real v) (hε i) (hAs i) (hBs i)
      (hAh i) (hBh i) (hrim i) (hU i) (hrimU i) (hgerm i)
  obtain ⟨r₀, hr₀, hr₀R, Q, hQheight, hsupport, hcentral, hmotion⟩ :=
    Saddle.Caps.exists_terminal_cylinder_straightening hv ht B hB hBi b
      (fun i => ⟨ε i, hε i, hBs i, hBh i⟩) hinj hR
  obtain ⟨ε₀, hε₀, hε₀i⟩ := exists_uniform_positive_lt ε hε
  obtain ⟨η₀, hη₀, hη₀i⟩ := exists_uniform_positive_lt η hη
  let r := min r₀ ε₀
  let δ := min η₀ r / 2
  have hr : 0 < r := lt_min hr₀ hε₀
  have hrr : r ≤ r₀ := min_le_left _ _
  have hre (i : ι) : r < ε i := (min_le_right _ _).trans_lt (hε₀i i)
  have hδ : 0 < δ := half_pos (lt_min hη₀ hr)
  have hδr : δ < r := by dsimp [δ]; linarith [min_le_right η₀ r]
  have hδη (i : ι) : δ < η i := by
    have hle := min_le_left η₀ r
    have hi := hη₀i i
    dsimp [δ]
    linarith
  let J : (S1 × Real) ≃ₜ (S1 × Real) :=
    (Homeomorph.refl S1).prodCongr (Homeomorph.addRight b)
  let T (i : ι) := J.toOpenPartialHomeomorph.trans (B i)
  let C (i : ι) := (T i).restrOpen (univ ×ˢ Ioo (-r) r) (isOpen_univ.prod isOpen_Ioo)
  have hC (i : ι) (q : S1) (z : Real) : C i (q, z) = B i (q, b + z) := by
    change B i (q, z + b) = _
    rw [add_comm z b]
  have hCs (i : ι) : (C i).source = univ ×ˢ Ioo (-r) r := by
    apply inter_eq_right.mpr
    rintro ⟨q, z⟩ ⟨_, hz⟩
    refine ⟨mem_univ _, ?_⟩
    change (q, z + b) ∈ (B i).source
    exact hBs i ⟨mem_univ _, by linarith [hz.1, hre i], by linarith [hz.2, hre i]⟩
  have hcyl (i : ι) (q : S1) (z : Real) (hz : z ∈ Ioo (-r) r) :
      Q (t (C i (q, z))) = (b + z) • v +
        ((Hemisphere.Plane v).orthogonalProjectionOnto (t (B i (q, b))) : E3) := by
    rw [hC, hmotion i z ⟨by linarith [hz.1], by linarith [hz.2]⟩ q]
    have hh := (heightCoordinates hv).apply_symm_apply (t (B i (q, b)))
    change inner Real v (t (B i (q, b))) • v +
      ((Hemisphere.Plane v).orthogonalProjectionOnto (t (B i (q, b))) : E3) = _ at hh
    rw [hBh i q b ⟨by linarith [hε i], by linarith [hε i]⟩] at hh
    nth_rw 1 [← hh]
    rw [add_smul]
    abel
  refine ⟨r, δ, hr, hrr.trans_lt hr₀R, hδ, hδr, hre, Q, C,
    hQheight, hsupport, hcentral, hCs, hC, hcyl, ?_, ?_, ?_⟩
  · intro i
    simpa only [hC, add_zero] using hboundary i
  · intro i q z hz
    rw [hC]
    exact hinside i q (b + z) ⟨by linarith [hz.1, hre i], by linarith [hz.2]⟩
  · intro i z hz
    have hzη : z ∈ Icc (b - η i) (b + η i) :=
      ⟨by linarith [hz.1, hδη i], by linarith [hz.2, hδη i]⟩
    have hzr : z - b ∈ Ioo (-r) r := ⟨by linarith [hz.1], by linarith [hz.2]⟩
    have hpoint (q : S1) : Q (t (B i (q, z))) = z • v +
        ((Hemisphere.Plane v).orthogonalProjectionOnto (t (B i (q, b))) : E3) := by
      have hh := hcyl i q (z - b) hzr
      rw [hC] at hh
      simpa only [add_sub_cancel] using hh
    have hprojection (q : S1) : (Hemisphere.Plane v).orthogonalProjectionOnto
        (Q (t (B i (q, z)))) =
        (Hemisphere.Plane v).orthogonalProjectionOnto (t (B i (q, b))) := by
      rw [hpoint]
      exact congrArg Prod.snd ((heightCoordinates hv).symm_apply_apply
        (z, (Hemisphere.Plane v).orthogonalProjectionOnto (t (B i (q, b)))))
    calc
      _ = (fun x => (Hemisphere.Plane v).orthogonalProjectionOnto (Q x)) ''
          range (fun q : S1 => s (A i (q, z))) := range_comp _ _
      _ = (fun x => (Hemisphere.Plane v).orthogonalProjectionOnto (Q x)) ''
          range (fun q : S1 => t (B i (q, z))) := by rw [hslices i z hzη]
      _ = range (fun q : S1 => (Hemisphere.Plane v).orthogonalProjectionOnto
          (t (B i (q, b)))) := by
        rw [← range_comp]
        exact congrArg Set.range (funext hprojection)
      _ = _ := by
        have hh := congrArg
          (fun S : Set E3 => (Hemisphere.Plane v).orthogonalProjectionOnto '' S) (hrim i)
        rw [← range_comp, ← range_comp] at hh
        exact hh.symm

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

end

end M38Schoenflies
