import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.TailSplice

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1
local notation "IR2" => 𝓘(Real, Real × Real)

def tailCoordinate (e : OpenPartialHomeomorph E2 S2)
    (F : OpenPartialHomeomorph (Real × Real) S2) (s : Real) : Real :=
  e.symm (F (s, 0)) 1

def rawTailCoordinates (e : OpenPartialHomeomorph E2 S2)
    (F : OpenPartialHomeomorph (Real × Real) S2) (z : Real × Real) : E2 :=
  WithLp.toLp 2 ![-Real.sqrt ((tailCoordinate e F z.2)^2 - z.1), tailCoordinate e F z.2]

def rawTailPoint (e : OpenPartialHomeomorph E2 S2)
    (F : OpenPartialHomeomorph (Real × Real) S2) (z : Real × Real) : S2 :=
  e (rawTailCoordinates e F z)

theorem exists_raw_tail_transport_neighborhood
    {height : S2 → Real} {c : Real}
    (e : OpenPartialHomeomorph E2 S2)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    (hform : ∀ u ∈ e.source, height (e u) = c - (u 0)^2 + (u 1)^2)
    (F : OpenPartialHomeomorph (Real × Real) S2)
    (hF : ContMDiffOn IR2 (𝓡 2) ∞ F F.source)
    (hheight : ∀ z ∈ F.source, height (F z) = c + z.2)
    (K : Set Real)
    (hK : ∀ s ∈ K, (s, 0) ∈ F.source ∧ F (s, 0) ∈ e.target ∧
      e.symm (F (s, 0)) 0 < 0) :
    ∃ W : Set (Real × Real), IsOpen W ∧ ({0} : Set Real) ×ˢ K ⊆ W ∧
      ContMDiffOn IR2 (𝓡 2) ∞ (rawTailPoint e F) W ∧
      MapsTo (rawTailPoint e F) W F.target ∧
      (∀ z ∈ W, height (rawTailPoint e F z) = c + z.1) ∧
      (∀ z ∈ W, e.symm (rawTailPoint e F z) 1 = tailCoordinate e F z.2) ∧
      ContDiffOn Real ∞ (rawTailCoordinates e F) W ∧
      MapsTo (rawTailCoordinates e F) W e.source ∧
      (∀ z ∈ W, rawTailCoordinates e F z 0 < 0) ∧
      ∀ s ∈ K, rawTailPoint e F (0, s) = F (s, 0) := by
  let S : Set Real := (fun s : Real => (s, (0 : Real))) ⁻¹'
    (F.source ∩ F ⁻¹' e.target)
  have hS : IsOpen S :=
    (F.continuousOn.isOpen_inter_preimage F.open_source e.open_target).preimage
      (continuous_id.prodMk continuous_const)
  have hbase : ContMDiffOn 𝓘(Real, Real) (𝓡 2) ∞
      (fun s => e.symm (F (s, 0))) S := by
    have hline : ContMDiff 𝓘(Real, Real) IR2 ∞ (fun s : Real => (s, (0 : Real))) :=
      (contDiff_id.prodMk contDiff_const).contMDiff
    exact hei.comp
      (hF.comp hline.contMDiffOn
        (fun s hs => hs.1)) (fun s hs => hs.2)
  have hy : ContDiffOn Real ∞ (tailCoordinate e F) S :=
    ((EuclideanSpace.proj (𝕜 := Real) (1 : Fin 2)).contMDiff.comp_contMDiffOn hbase).contDiffOn
  let T : Set (Real × Real) := Prod.snd ⁻¹' S
  have hT : IsOpen T := hS.preimage continuous_snd
  have hyT : ContDiffOn Real ∞ (fun z : Real × Real => tailCoordinate e F z.2) T :=
    hy.comp contDiff_snd.contDiffOn (fun z hz => hz)
  have hq : ContDiffOn Real ∞
      (fun z : Real × Real => (tailCoordinate e F z.2)^2 - z.1) T :=
    (hyT.pow 2).sub contDiff_fst.contDiffOn
  let W₀ : Set (Real × Real) := T ∩
    {z : Real × Real | 0 < (tailCoordinate e F z.2)^2 - z.1}
  have hW₀ : IsOpen W₀ := hq.continuousOn.isOpen_inter_preimage hT isOpen_Ioi
  have hraw : ContDiffOn Real ∞ (rawTailCoordinates e F) W₀ := by
    apply (contDiffOn_piLp 2).mpr
    intro i
    fin_cases i
    · exact ((hq.mono inter_subset_left).sqrt (fun z hz => ne_of_gt hz.2)).neg
    · exact hyT.mono inter_subset_left
  let W₁ := W₀ ∩ rawTailCoordinates e F ⁻¹' e.source
  have hW₁ : IsOpen W₁ := hraw.continuousOn.isOpen_inter_preimage hW₀ e.open_source
  have hpoint : ContMDiffOn IR2 (𝓡 2) ∞ (rawTailPoint e F) W₁ :=
    he.comp (hraw.mono inter_subset_left).contMDiffOn (fun z hz => hz.2)
  let W := W₁ ∩ rawTailPoint e F ⁻¹' F.target
  have hW : IsOpen W := hpoint.continuousOn.isOpen_inter_preimage hW₁ F.open_target
  have hzero (s : Real) (hs : s ∈ K) :
      rawTailCoordinates e F (0, s) = e.symm (F (s, 0)) ∧
      0 < (tailCoordinate e F s)^2 := by
    obtain ⟨hsF, hsE, hsneg⟩ := hK s hs
    have hscoord := e.map_target hsE
    have hlevel := hform _ hscoord
    rw [e.right_inv hsE, hheight (s, 0) hsF] at hlevel
    have hsquare : (tailCoordinate e F s)^2 = (e.symm (F (s, 0)) 0)^2 := by
      change (e.symm (F (s, 0)) 1)^2 = _
      linarith
    refine ⟨?_, hsquare ▸ sq_pos_of_ne_zero (ne_of_lt hsneg)⟩
    ext i
    fin_cases i
    · change -Real.sqrt ((tailCoordinate e F s)^2 - 0) = e.symm (F (s, 0)) 0
      rw [sub_zero, hsquare, Real.sqrt_sq_eq_abs, abs_of_neg hsneg, neg_neg]
    · rfl
  have hzero_point (s : Real) (hs : s ∈ K) : rawTailPoint e F (0, s) = F (s, 0) := by
    change e (rawTailCoordinates e F (0, s)) = _
    rw [(hzero s hs).1, e.right_inv (hK s hs).2.1]
  refine ⟨W, hW, ?_, hpoint.mono inter_subset_left, fun z hz => hz.2, ?_, ?_,
    hraw.mono (fun z hz => hz.1.1), fun z hz => hz.1.2, ?_, hzero_point⟩
  · rintro ⟨t, s⟩ ⟨ht, hs⟩
    have ht0 : t = 0 := ht
    subst t
    refine ⟨⟨⟨⟨(hK s hs).1, (hK s hs).2.1⟩, ?_⟩, ?_⟩, ?_⟩
    · change 0 < (tailCoordinate e F s)^2 - 0
      simpa only [sub_zero] using (hzero s hs).2
    · change rawTailCoordinates e F (0, s) ∈ e.source
      rw [(hzero s hs).1]
      exact e.map_target (hK s hs).2.1
    · change rawTailPoint e F (0, s) ∈ F.target
      rw [hzero_point s hs]
      exact F.map_source (hK s hs).1
  · intro z hz
    change height (e (rawTailCoordinates e F z)) = c + z.1
    rw [hform _ hz.1.2]
    change c - (-Real.sqrt ((tailCoordinate e F z.2)^2 - z.1))^2 +
      (tailCoordinate e F z.2)^2 = c + z.1
    rw [neg_sq, Real.sq_sqrt hz.1.1.2.le]
    ring
  · intro z hz
    change e.symm (e (rawTailCoordinates e F z)) 1 = _
    rw [e.left_inv hz.1.2]
    rfl
  · intro z hz
    change -Real.sqrt ((tailCoordinate e F z.2)^2 - z.1) < 0
    exact neg_neg_of_pos (Real.sqrt_pos.mpr hz.1.1.2)

end Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior
