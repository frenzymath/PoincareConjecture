import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.ComponentSourceAxis
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.SourceStripFibers
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.SignedAxisMonodromy

set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D2" => closedBall (0 : V2) 1

theorem ComponentBranchModel.exists_self_paired_source_strips
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {f : V2 → X} {R : Set X}
    {old : OrdinaryDoubleCurveModel e f R} {i : old.Index}
    (D : ComponentBranchModel old i) (hself : old.mate i = i) (hcore : D.core ⊆ interior R)
    {n : ℕ} (t : Fin (n + 3) → ℝ) (ht : StrictMono t)
    (L : Fin (n + 2) → SimplicialComplex ℝ (D.sample → ℝ × V3))
    (hL : ∀ k, (L k).faces.Finite) (hLK : ∀ k, (L k).space ⊆ D.complex.space)
    (x y : Fin (n + 2) → V2) (C : ∀ k, RawCrossingChart e f R (x k) (y k))
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
    (haxisimage : (fun s => sigma ((0, 0), s)) '' Icc (t 0) (t (Fin.last (n + 2))) = D.axis.space)
    {m : ℕ} (P : Polygon V2 (m + 3)) (hP : P.HasSimplicialEdges)
    (hinjP : Function.Injective P) (hPs : P.boundary ℝ = old.pieces i) :
    closing.swap = true ∧ closing.sign 0 = closing.sign 1 ∧
    ∃ phi : Fin 2 → P2 → V2,
      (∀ j, FinitePiecewiseAffineOn (phi j)
        (Icc (-1 : ℝ) 1 ×ˢ Icc (t 0) (t (Fin.last (n + 2))))) ∧
      (∀ j z, z ∈ Icc (-1 : ℝ) 1 ×ˢ Icc (t 0) (t (Fin.last (n + 2))) →
        phi j z ∈ D2 ∧ f (phi j z) = (D.inverse (sigma (signedSheetStripMap j z)) : X) ∧
          D.graph (f (phi j z)) = sigma (signedSheetStripMap j z)) ∧
      (D2 ∩ f ⁻¹' ((fun z => (D.inverse (sigma z) : X)) ''
        (signedTubeDiamond ×ˢ Icc (t 0) (t (Fin.last (n + 2))))) =
        ⋃ j, phi j '' (Icc (-1 : ℝ) 1 ×ˢ Icc (t 0) (t (Fin.last (n + 2))))) ∧
      (∀ j z, z ∈ Icc (-1 : ℝ) 1 ×ˢ Icc (t 0) (t (Fin.last (n + 2))) →
        (phi j z ∈ old.pieces i ↔ z.1 = 0)) ∧
      (∀ j u, u ∈ Icc (-1 : ℝ) 1 →
        phi j (u, t 0) = phi (closing.index j)
          ((if closing.sign j.rev then u else -u), t (Fin.last (n + 2)))) ∧
      (∀ j k z, z ∈ Icc (-1 : ℝ) 1 ×ˢ Icc (t 0) (t (Fin.last (n + 2))) →
        ∀ w, w ∈ Icc (-1 : ℝ) 1 ×ˢ Icc (t 0) (t (Fin.last (n + 2))) →
        (phi j z = phi k w ↔ (j = k ∧ z = w) ∨
          (z.2 = t 0 ∧ w.2 = t (Fin.last (n + 2)) ∧ k = closing.index j ∧
            w.1 = (if closing.sign j.rev then z.1 else -z.1)) ∨
          (w.2 = t 0 ∧ z.2 = t (Fin.last (n + 2)) ∧ j = closing.index k ∧
            z.1 = (if closing.sign k.rev then w.1 else -w.1)))) ∧
      ((⋃ j, phi j '' (Icc (-1 : ℝ) 1 ×ˢ Icc (t 0) (t (Fin.last (n + 2))))) ∩
        doubleLocusOn f D2) = old.pieces i := by
  obtain ⟨phi, hPL, hvalue, _hbranch, hsep, hwhole, hunique⟩ :=
    D.exists_cut_source_strips hcore t ht L hL hLK x y C hLC sigma hsigma himage label hcoords
  have hab : t 0 < t (Fin.last (n + 2)) := ht (by change 0 < n + 2; omega)
  have hclosing (z : P2) (hz : z ∈ signedTubeDiamond) :
      sigma (z, t 0) = sigma (closing.linear z, t (Fin.last (n + 2))) :=
    (hfib ⟨(z, t 0), hz, le_rfl, hab.le⟩
      ⟨(closing.linear z, t (Fin.last (n + 2))), (closing.mem_diamond z).mp hz, hab.le, le_rfl⟩).mpr
        (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))
  have hclose := source_strip_closing_of_physical_closing f
    (fun z => (D.inverse z : X)) sigma hab closing hclosing phi hPL
      (fun j z hz => (hvalue j z hz).1) (fun j z hz => (hvalue j z hz).2.1) hunique
  have hselected := D.source_strip_selected_iff hself sigma haxis phi hvalue
  have hcover := D.source_strip_axis_cover hself sigma haxis haxisimage phi hvalue hwhole
  have hzero : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := by norm_num
  have haxisfib := source_axis_fibers_of_signed_tube sigma hab closing hfib phi (D.graph ∘ f)
    (fun j s hs => by simpa [signedSheetStripMap_apply] using (hvalue j (0, s) ⟨hzero, hs⟩).2.2)
    (fun j s hs => hsep j (0, s) ⟨hzero, hs⟩)
    (fun j => by simpa using hclose j 0 hzero)
  have hswap : closing.swap = true := signed_axis_closing_swaps_of_connected_source closing hab
    (fun j s => phi j (0, s))
    (fun j => (hPL j).continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun s hs => ⟨hzero, hs⟩))
    (old.pieces i) (old.connected i).isPreconnected
    (by simpa [Set.iUnion_fin_add_one_eq_iUnion_succ] using hcover.symm)
    (fun j k s hs v hv => by simpa only [Subtype.mk.injEq] using haxisfib j k ⟨s, hs⟩ ⟨v, hv⟩)
  have hinj := source_strip_injOn_open_of_signed_tube sigma closing hfib phi (D.graph ∘ f)
    (fun j z hz => (hvalue j z hz).2.2)
  have hsign : closing.sign 0 = closing.sign 1 := by
    rcases signed_axis_closing_classification_from_source_strips P hP hinjP (by norm_num) hab
      phi hPL hinj (by simpa only [hPs] using hselected) closing hclose with h | h
    · have hh := congrArg SignedAxisPermutation.swap h
      rw [hswap] at hh
      cases hh
    · exact h.2
  have htrace : ((⋃ j, phi j '' (Icc (-1 : ℝ) 1 ×ˢ Icc (t 0) (t (Fin.last (n + 2))))) ∩
      doubleLocusOn f D2) = old.pieces i := by
    ext w
    constructor
    · rintro ⟨hw, hwdouble⟩
      obtain ⟨j, z, hz, rfl⟩ := mem_iUnion.mp hw
      by_cases hzero : z.1 = 0
      · exact (hselected j z hz).mpr hzero
      · obtain ⟨_, v, hv, hfv, hne⟩ := hwdouble
        have heq := hunique j z hz hzero v hv (hfv.symm.trans (hvalue j z hz).2.1)
        exact (hne heq.symm).elim
    · intro hw
      obtain ⟨j, s, hs, hsw⟩ := mem_iUnion.mp (hcover.symm.subset hw)
      exact ⟨mem_iUnion.mpr ⟨j, (0, s), ⟨hzero, hs⟩, hsw⟩, old.piece_subset_double i hw⟩
  exact ⟨hswap, hsign, phi, hPL, hvalue, hwhole, hselected, hclose,
    source_strip_fibers_of_signed_tube sigma closing hfib phi (D.graph ∘ f)
      (fun j z hz => (hvalue j z hz).2.2) hsep hclose, htrace⟩

end PoincareConjecture.M76.Dehn
