import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Tubes.Strips.PairedComponents
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.SourceStripFibers
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Tubes.Monodromy.PlanarClosing



set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli
local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)



theorem ComponentBranchModel.exists_paired_source_strips
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {f : P2 → X} {R : Set X}
    {S : Set P2} {old : SourceCircleDecomposition f S} {i : old.Index}
    (D : ComponentBranchModel (e := e) (R := R) old i) (hmate : old.mate i ≠ i) (hcore : D.core ⊆ interior R)
    {n : ℕ} (t : Fin (n + 3) → ℝ) (ht : StrictMono t)
    (L : Fin (n + 2) → SimplicialComplex ℝ (D.sample → ℝ × V3))
    (hL : ∀ k, (L k).faces.Finite) (hLK : ∀ k, (L k).space ⊆ D.complex.space)
    (x y : Fin (n + 2) → P2) (C : ∀ k, RawSourceCrossing e f S R (x k) (y k))
    (hLC : ∀ k, MapsTo (fun z ↦ (D.inverse z : X)) (L k).space (C k).chart.source)
    (sigma : P2 × ℝ → (D.sample → ℝ × V3))
    (hsigma : ∀ k : Fin (n + 2), FinitePiecewiseAffineOn sigma
      (signedTubeDiamond ×ˢ Icc (t k.castSucc) (t k.succ)))
    (himage : ∀ k, MapsTo sigma
      (signedTubeDiamond ×ˢ Icc (t k.castSucc) (t k.succ)) (L k).space)
    (label : Fin (n + 2) → Equiv.Perm (Fin 2))
    (hcoords : ∀ k j z, z ∈ signedTubeDiamond ×ˢ Icc (t k.castSucc) (t k.succ) →
      ((C k).chart (D.inverse (sigma z)) (label k j).castSucc = 0 ↔
        z.1 ∈ signedTubeSheet j))
    (closing : SignedAxisPermutation)
    (hfib : ∀ z w : ↥(signedTubeDiamond ×ˢ Icc (t 0) (t (Fin.last (n + 2)))),
      sigma z = sigma w ↔ z = w ∨
        ((z : P2 × ℝ).2 = t 0 ∧ (w : P2 × ℝ).2 = t (Fin.last (n + 2)) ∧
          closing.linear (z : P2 × ℝ).1 = (w : P2 × ℝ).1) ∨
        ((w : P2 × ℝ).2 = t 0 ∧ (z : P2 × ℝ).2 = t (Fin.last (n + 2)) ∧
          closing.linear (w : P2 × ℝ).1 = (z : P2 × ℝ).1))
    (haxis : ∀ z ∈ signedTubeDiamond ×ˢ Icc (t 0) (t (Fin.last (n + 2))),
      sigma z ∈ D.axis.space ↔ z.1 = (0, 0))
    (haxisimage : (fun s => sigma ((0, 0), s)) '' Icc (t 0) (t (Fin.last (n + 2))) = D.axis.space) :
    closing = SignedAxisPermutation.refl ∧
    ∃ (label : Equiv.Perm (Fin 2)) (phi : Fin 2 → P2 → P2),
      (∀ j, FinitePiecewiseAffineOn (phi j)
        (Icc (-1 : ℝ) 1 ×ˢ Icc (t 0) (t (Fin.last (n + 2))))) ∧
      (∀ j z, z ∈ Icc (-1 : ℝ) 1 ×ˢ Icc (t 0) (t (Fin.last (n + 2))) →
        phi j z ∈ S ∧ f (phi j z) = (D.inverse (sigma (signedSheetStripMap j z)) : X) ∧
          D.graph (f (phi j z)) = sigma (signedSheetStripMap j z)) ∧
      (S ∩ f ⁻¹' ((fun z ↦ (D.inverse (sigma z) : X)) ''
        (signedTubeDiamond ×ˢ Icc (t 0) (t (Fin.last (n + 2))))) =
        ⋃ j, phi j '' (Icc (-1 : ℝ) 1 ×ˢ Icc (t 0) (t (Fin.last (n + 2))))) ∧
      (∀ j z, z ∈ Icc (-1 : ℝ) 1 ×ˢ Icc (t 0) (t (Fin.last (n + 2))) →
        (phi j z ∈ (if label j = 0 then old.pieces i else old.pieces (old.mate i)) ↔
          z.1 = 0)) ∧
      (∀ j, (fun s ↦ phi j (0, s)) '' Icc (t 0) (t (Fin.last (n + 2))) =
        if label j = 0 then old.pieces i else old.pieces (old.mate i)) ∧
      (∀ j k z, z ∈ Icc (-1 : ℝ) 1 ×ˢ Icc (t 0) (t (Fin.last (n + 2))) →
        ∀ w, w ∈ Icc (-1 : ℝ) 1 ×ˢ Icc (t 0) (t (Fin.last (n + 2))) →
        (phi j z = phi k w ↔ j = k ∧ z.1 = w.1 ∧
          (z.2 = w.2 ∨ (z.2 = t 0 ∧ w.2 = t (Fin.last (n + 2))) ∨
            (w.2 = t 0 ∧ z.2 = t (Fin.last (n + 2)))))) ∧
      ((⋃ j, phi j '' (Icc (-1 : ℝ) 1 ×ˢ Icc (t 0) (t (Fin.last (n + 2))))) ∩
        doubleLocusOn f S) = old.pieces i ∪ old.pieces (old.mate i) := by
  classical
  obtain ⟨phi, hPL, hvalue, _hbranch, hsep, hwhole, hunique⟩ :=
    D.exists_cut_source_strips hcore t ht L hL hLK x y C hLC sigma hsigma himage label hcoords
  have hab : t 0 < t (Fin.last (n + 2)) := ht (by change 0 < n + 2; omega)
  have hclosing (z : P2) (hz : z ∈ signedTubeDiamond) :
      sigma (z, t 0) = sigma (closing.linear z, t (Fin.last (n + 2))) :=
    (hfib ⟨(z, t 0), hz, le_rfl, hab.le⟩
      ⟨(closing.linear z, t (Fin.last (n + 2))), (closing.mem_diamond z).mp hz, hab.le, le_rfl⟩).mpr
        (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))
  have hclose := source_strip_closing_of_physical_closing f
    (fun z ↦ (D.inverse z : X)) sigma hab closing hclosing phi hPL
      (fun j z hz ↦ (hvalue j z hz).1) (fun j z hz ↦ (hvalue j z hz).2.1) hunique
  have hselected := D.source_strip_selected_pair_iff sigma haxis phi hvalue
  have hcover := D.source_strip_axis_pair_cover sigma haxis haxisimage phi hvalue hwhole
  have hzero : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := by norm_num
  obtain ⟨hswap, labels, hlabels, hmiddle⟩ := old.paired_source_strip_components i hmate hab phi
    (fun j ↦ (hPL j).continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun s hs ↦ ⟨hzero, hs⟩)) hcover hselected closing
    (fun j ↦ by simpa using hclose j 0 hzero)
  have hinj := source_strip_injOn_open_of_signed_tube sigma closing hfib phi (D.graph ∘ f)
    (fun j z hz ↦ (hvalue j z hz).2.2)
  let idx : Fin 2 → old.Index := fun j ↦ if labels j = 0 then i else old.mate i
  have hmid (j : Fin 2) (z : P2)
      (hz : z ∈ Icc (-1 : ℝ) 1 ×ˢ Icc (t 0) (t (Fin.last (n + 2)))) :
      phi j z ∈ (old.polygon (idx j)).boundary ℝ ↔ z.1 = 0 := by
    have h := hmiddle j z hz
    change phi j z ∈ old.pieces (idx j) ↔ z.1 = 0
    by_cases hj : labels j = 0
    · rw [show idx j = i from if_pos hj]
      simpa only [if_pos hj] using h
    · rw [show idx j = old.mate i from if_neg hj]
      simpa only [if_neg hj] using h
  have hid : closing = SignedAxisPermutation.refl :=
    signed_axis_closing_eq_refl_of_planar_strips (fun j ↦ old.n (idx j))
      (fun j ↦ old.polygon (idx j)) (fun j ↦ (old.model (idx j)).2.1)
      (fun j ↦ (old.model (idx j)).1) (by norm_num) hab phi hPL hinj hmid closing hswap hclose
  have hsourceFib := source_strip_fibers_of_signed_tube sigma closing hfib phi (D.graph ∘ f)
    (fun j z hz ↦ (hvalue j z hz).2.2) hsep hclose
  refine ⟨hid, labels, phi, hPL, hvalue, hwhole, hmiddle, hlabels, ?_, ?_⟩
  · intro j k z hz w hw
    have h := hsourceFib j k z hz w hw
    simp only [hid, SignedAxisPermutation.refl, SignedAxisPermutation.index,
      jointSheetIndex, if_true] at h
    rw [h]
    constructor
    · rintro (⟨hjk, hzw⟩ | ⟨hz0, hwb, hkj, hwu⟩ | ⟨hw0, hzb, hjk, hzu⟩)
      · exact ⟨hjk, congrArg Prod.fst hzw, Or.inl (congrArg Prod.snd hzw)⟩
      · exact ⟨hkj.symm, hwu.symm, Or.inr (Or.inl ⟨hz0, hwb⟩)⟩
      · exact ⟨hjk, hzu, Or.inr (Or.inr ⟨hw0, hzb⟩)⟩
    · rintro ⟨hjk, hzu, ht | ht | ht⟩
      · exact Or.inl ⟨hjk, Prod.ext hzu ht⟩
      · exact Or.inr (Or.inl ⟨ht.1, ht.2, hjk.symm, hzu.symm⟩)
      · exact Or.inr (Or.inr ⟨ht.1, ht.2, hjk, hzu⟩)
  · ext w
    constructor
    · rintro ⟨hw, hwdouble⟩
      obtain ⟨j, z, hz, rfl⟩ := mem_iUnion.mp hw
      by_cases hz0 : z.1 = 0
      · exact (hselected j z hz).mpr hz0
      · obtain ⟨_, v, hv, hfv, hne⟩ := hwdouble
        have heq := hunique j z hz hz0 v hv (hfv.symm.trans (hvalue j z hz).2.1)
        exact (hne heq.symm).elim
    · intro hw
      obtain ⟨j, s, hs, hsw⟩ := mem_iUnion.mp (hcover.symm.subset hw)
      refine ⟨mem_iUnion.mpr ⟨j, (0, s), ⟨hzero, hs⟩, hsw⟩, ?_⟩
      exact hw.elim (fun h ↦ old.piece_subset_double i h)
        (fun h ↦ old.piece_subset_double (old.mate i) h)

end PoincareConjecture.M76.Dehn.Annuli
