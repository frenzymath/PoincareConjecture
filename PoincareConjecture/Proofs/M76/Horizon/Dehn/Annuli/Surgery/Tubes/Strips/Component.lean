import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Tubes.Strips.Local
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.SourceStripGluing

set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem ComponentBranchModel.exists_cut_source_strips
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] {S : Set E}
    {e : ι → OpenPartialHomeomorph X V3} {f : E → X} {R : Set X}
    {old : SourceCircleDecomposition f S} {i : old.Index}
    (D : ComponentBranchModel (e := e) (R := R) old i) (hcore : D.core ⊆ interior R)
    {n : ℕ} (t : Fin (n + 3) → ℝ) (ht : StrictMono t)
    (L : Fin (n + 2) → SimplicialComplex ℝ (D.sample → ℝ × V3))
    (hL : ∀ k, (L k).faces.Finite) (hLK : ∀ k, (L k).space ⊆ D.complex.space)
    (x y : Fin (n + 2) → E) (C : ∀ k, RawSourceCrossing e f S R (x k) (y k))
    (hLC : ∀ k, MapsTo (fun z ↦ (D.inverse z : X)) (L k).space (C k).chart.source)
    (sigma : P2 × ℝ → (D.sample → ℝ × V3))
    (hsigma : ∀ k : Fin (n + 2), FinitePiecewiseAffineOn sigma
      (signedTubeDiamond ×ˢ Icc (t k.castSucc) (t k.succ)))
    (himage : ∀ k, MapsTo sigma
      (signedTubeDiamond ×ˢ Icc (t k.castSucc) (t k.succ)) (L k).space)
    (label : Fin (n + 2) → Equiv.Perm (Fin 2))
    (hcoords : ∀ k j z, z ∈ signedTubeDiamond ×ˢ Icc (t k.castSucc) (t k.succ) →
      ((C k).chart (D.inverse (sigma z)) (label k j).castSucc = 0 ↔
        z.1 ∈ signedTubeSheet j)) :
    ∃ phi : Fin 2 → P2 → E,
      (∀ j, FinitePiecewiseAffineOn (phi j)
        (Icc (-1 : ℝ) 1 ×ˢ Icc (t 0) (t (Fin.last (n + 2))))) ∧
      (∀ j z, z ∈ Icc (-1 : ℝ) 1 ×ˢ Icc (t 0) (t (Fin.last (n + 2))) →
        phi j z ∈ S ∧
        f (phi j z) = (D.inverse (sigma (signedSheetStripMap j z)) : X) ∧
        D.graph (f (phi j z)) = sigma (signedSheetStripMap j z)) ∧
      (∀ k j z, z ∈ Icc (-1 : ℝ) 1 ×ˢ Icc (t k.castSucc) (t k.succ) →
        phi j z ∈ (if label k j = 0 then (C k).left else (C k).right)) ∧
      (∀ j z, z ∈ Icc (-1 : ℝ) 1 ×ˢ Icc (t 0) (t (Fin.last (n + 2))) →
        phi j z ≠ phi j.rev z) ∧
      S ∩ f ⁻¹' ((fun z => (D.inverse (sigma z) : X)) ''
        (signedTubeDiamond ×ˢ Icc (t 0) (t (Fin.last (n + 2))))) =
        (⋃ j, phi j '' (Icc (-1 : ℝ) 1 ×ˢ Icc (t 0) (t (Fin.last (n + 2))))) ∧
      ∀ j z, z ∈ Icc (-1 : ℝ) 1 ×ˢ Icc (t 0) (t (Fin.last (n + 2))) →
        z.1 ≠ 0 → ∀ w ∈ S,
          f w = (D.inverse (sigma (signedSheetStripMap j z)) : X) → w = phi j z := by
  classical
  have hex (j : Fin 2) (k : Fin (n + 2)) := D.exists_local_source_strip hcore
    (L k) (hL k) (hLK k) (C k) (hLC k) (ht Fin.castSucc_lt_succ)
      sigma (hsigma k) (himage k) j (label k j)
      (fun z hz => (hcoords k j _ (signedSheetStripMap_mem j hz)).mpr
        (signedSheetStripMap_sheet j hz))
  choose localMap hPL hlocal using hex
  have hunique (j : Fin 2) (k : Fin (n + 2)) (z : P2)
      (hz : z ∈ Icc (-1 : ℝ) 1 ×ˢ Icc (t k.castSucc) (t k.succ)) (hne : z.1 ≠ 0)
      (w : E) (hw : w ∈ S)
      (hwf : f w = (D.inverse (sigma (signedSheetStripMap j z)) : X)) :
      w = localMap j k z := by
    have hval := hlocal j k z hz
    have hpoint : f (localMap j k z) ∈ (C k).chart.source := by
      rw [hval.2.2.1]
      exact hLC k (himage k (signedSheetStripMap_mem j hz))
    have hnot : (signedSheetStripMap j z).1 ∉ signedTubeSheet j.rev := by
      rw [signedTubeSheet_coordinate_iff _ (signedSheetStripMap_mem j hz).1]
      fin_cases j <;> simpa [signedSheetStripMap_apply, Fin.rev] using hne
    have hc : (C k).chart (f (localMap j k z)) (label k j.rev).castSucc ≠ 0 := by
      rw [hval.2.2.1]
      exact fun h => hnot ((hcoords k j.rev _ (signedSheetStripMap_mem j hz)).mp h)
    have hc' : (C k).chart (f (localMap j k z)) 0 ≠ 0 ∨
        (C k).chart (f (localMap j k z)) 1 ≠ 0 := by
      by_cases h : label k j.rev = 0
      · left
        simpa [h] using hc
      · right
        have h' : label k j.rev = 1 := by omega
        simpa [h'] using hc
    exact ((C k).eq_of_coordinate_ne hval.1 hw hpoint
      (hval.2.2.1.trans hwf.symm) hc').symm
  have hglue (j : Fin 2) := exists_source_strip_gluing f
    (fun z => (D.inverse (sigma (signedSheetStripMap j z)) : X)) t ht (localMap j)
      (hPL j) (fun k z hz => (hlocal j k z hz).1)
      (fun k z hz => (hlocal j k z hz).2.2.1) (hunique j)
  choose phi hphiPL hphiLocal hphiD hphiValue using hglue
  refine ⟨phi, hphiPL, ?_, ?_, ?_, ?_, ?_⟩
  · intro j z hz
    obtain ⟨k, hk⟩ := ht.monotone.exists_mem_consecutive_Icc hz.2
    have hz' : z ∈ Icc (-1 : ℝ) 1 ×ˢ Icc (t k.castSucc) (t k.succ) := ⟨hz.1, hk⟩
    refine ⟨hphiD j hz, hphiValue j z hz, ?_⟩
    rw [hphiLocal j k z hz']
    exact (hlocal j k z hz').2.2.2.1
  · intro k j z hz
    rw [hphiLocal j k z hz]
    exact (hlocal j k z hz).2.1
  · intro j z hz heq
    obtain ⟨k, hk⟩ := ht.monotone.exists_mem_consecutive_Icc hz.2
    have hz' : z ∈ Icc (-1 : ℝ) 1 ×ˢ Icc (t k.castSucc) (t k.succ) := ⟨hz.1, hk⟩
    have hmem := (hlocal j k z hz').2.1
    have hmem' := (hlocal j.rev k z hz').2.1
    rw [← hphiLocal j k z hz'] at hmem
    rw [← hphiLocal j.rev k z hz'] at hmem'
    have hlabels : label k j ≠ label k j.rev := by
      intro h
      have hh := (label k).injective h
      fin_cases j <;> simp [Fin.rev] at hh
    by_cases h : label k j = 0
    · have h' : label k j.rev ≠ 0 := fun h' => hlabels (h.trans h'.symm)
      simp only [h, h', if_pos, if_false] at hmem hmem'
      exact (C k).disjoint.notMem_of_mem_left hmem (heq ▸ hmem')
    · have h' : label k j.rev = 0 := by omega
      simp only [h, h', if_pos, if_false] at hmem hmem'
      exact (C k).disjoint.notMem_of_mem_left hmem' (heq ▸ hmem)
  · ext w
    constructor
    · rintro ⟨hw, z, hz, hzf⟩
      obtain ⟨k, hk⟩ := ht.monotone.exists_mem_consecutive_Icc hz.2
      have hz' : z ∈ signedTubeDiamond ×ˢ Icc (t k.castSucc) (t k.succ) := ⟨hz.1, hk⟩
      have hpoint : (D.inverse (sigma z) : X) ∈ (C k).chart.source :=
        hLC k (himage k hz')
      have hbranches := (C k).whole_preimage.subset
        ⟨hw, show f w ∈ (C k).chart.source from hzf ▸ hpoint⟩
      have hcase (ell : Fin 2)
          (hwbranch : w ∈ (if ell = 0 then (C k).left else (C k).right)) :
          w ∈ ⋃ j, phi j '' (Icc (-1 : ℝ) 1 ×ˢ Icc (t 0) (t (Fin.last (n + 2)))) := by
        let j := (label k).symm ell
        have hj : label k j = ell := (label k).apply_symm_apply ell
        have hcoord : (C k).chart (D.inverse (sigma z)) (label k j).castSucc = 0 := by
          rw [hj]
          fin_cases ell
          · exact ((C k).left_image _ hpoint).mp ⟨w, hwbranch, hzf.symm⟩ |>.1
          · exact ((C k).right_image _ hpoint).mp ⟨w, hwbranch, hzf.symm⟩ |>.1
        obtain ⟨u, hu, huz⟩ := signedSheetStripMap_surjective_on_sheet j hz'
          ((hcoords k j z hz').mp hcoord)
        have hu' : u ∈ Icc (-1 : ℝ) 1 ×ˢ Icc (t 0) (t (Fin.last (n + 2))) :=
          ⟨hu.1, (ht.monotone (Fin.zero_le _)).trans hu.2.1,
            hu.2.2.trans (ht.monotone (Fin.le_last _))⟩
        have hwf : f w = (D.inverse (sigma (signedSheetStripMap j u)) : X) := by
          rw [huz]
          exact hzf.symm
        have hwu := (hlocal j k u hu).2.2.2.2 w (by simpa only [hj] using hwbranch) hwf
        exact mem_iUnion.mpr ⟨j, u, hu', (hphiLocal j k u hu).trans hwu.symm⟩
      exact hbranches.elim (hcase 0) (hcase 1)
    · intro hw
      obtain ⟨j, u, hu, rfl⟩ := mem_iUnion.mp hw
      exact ⟨hphiD j hu, signedSheetStripMap j u, signedSheetStripMap_mem j hu,
        (hphiValue j u hu).symm⟩
  · intro j z hz hne w hw hwf
    obtain ⟨k, hk⟩ := ht.monotone.exists_mem_consecutive_Icc hz.2
    have hz' : z ∈ Icc (-1 : ℝ) 1 ×ˢ Icc (t k.castSucc) (t k.succ) := ⟨hz.1, hk⟩
    exact (hunique j k z hz' hne w hw hwf).trans (hphiLocal j k z hz').symm

end PoincareConjecture.M76.Dehn.Annuli
