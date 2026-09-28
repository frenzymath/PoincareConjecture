import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Tubes.Monodromy.SelfPairedStrips
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Tubes.SourceAnnuli.ReflectedCut

set_option autoImplicit false
open Set Metric Geometry Topology PLAnnularStrip Dehn

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)

structure ComponentReflectionAnnulusData
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {f : P2 → X} {S : Set P2} {R : Set X}
    (old : SourceCircleDecomposition f S) (i : old.Index) (L d : ℝ) where
  depth_pos : 0 < d
  width_small : 4 * d < L
  tube : P2 × ℝ → X
  source : Set P2
  chart : squareAnnulus L d ≃ₜ source
  tube_PL : PolyhedralPLInCharts e tube (singleReflectionTube L d)
  tube_fibers : ∀ z ∈ singleReflectionTube L d, ∀ w ∈ singleReflectionTube L d,
    tube z = tube w ↔ z = w ∨
      (z.1 = (w.1.1, -w.1.2) ∧ ((z.2 = 0 ∧ w.2 = 2 * L) ∨ (z.2 = 2 * L ∧ w.2 = 0)))
  tube_interior : tube '' singleReflectionTube L d ⊆ interior R
  source_interior : source ⊆ interior S
  chart_PL : chart.IsFinitePL
  chart_inverse_PL : chart.symm.IsFinitePL
  period_value : ∀ s ∈ Icc 0 (4 * L), ∀ u : Icc (-d) d,
    f (chart ⟨annulusMap L (by linarith [depth_pos, width_small]) ((s : AddCircle (4 * L)), u),
      _root_.Dehn.annulus_period_point_mem depth_pos width_small _ u⟩) =
      if s ≤ 2 * L then tube ((u, u), s) else tube ((u, -u), s - 2 * L)
  full_preimage : S ∩ f ⁻¹' (tube '' singleReflectionTube L d) = source
  double_trace : source ∩ doubleLocusOn f S = old.pieces i
  middle : ∀ p : squareAnnulus L d, (chart p : P2) ∈ old.pieces i ↔ depth L p = 0

theorem ComponentReflectionAnnulusData.middle_image
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {f : P2 → X} {S : Set P2} {R : Set X}
    {old : SourceCircleDecomposition f S} {i : old.Index} {L d : ℝ}
    (D : ComponentReflectionAnnulusData (e := e) (R := R) old i L d) :
    (fun p : squareAnnulus L d ↦ (D.chart p : P2)) '' {p | depth L p = 0} = old.pieces i := by
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact (D.middle p).mpr hp
  · intro hx
    have hxS : x ∈ D.source := (D.double_trace.symm.subset hx).1
    refine ⟨D.chart.symm ⟨x, hxS⟩, ?_, ?_⟩
    · apply (D.middle _).mp
      simpa only [Homeomorph.apply_symm_apply] using hx
    · exact congrArg Subtype.val (D.chart.apply_symm_apply _)

theorem ComponentBranchModel.nonempty_reflected_annulus_of_cyclic_map
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {f : P2 → X} {S : Set P2} {R : Set X}
    {old : SourceCircleDecomposition f S} {i : old.Index}
    (D : ComponentBranchModel (e := e) (R := R) old i) (hself : old.mate i = i) (hcore : D.core ⊆ interior R)
    (hfront : ∀ x ∈ S, f x ∈ frontier R ↔ x ∈ frontier S)
    {n : ℕ} (t : Fin (n + 3) → ℝ) (ht : StrictMono t)
    (K : Fin (n + 2) → SimplicialComplex ℝ (D.sample → ℝ × V3))
    (hK : ∀ k, (K k).faces.Finite) (hKK : ∀ k, (K k).space ⊆ D.complex.space)
    (x y : Fin (n + 2) → P2) (C : ∀ k, RawSourceCrossing e f S R (x k) (y k))
    (hKC : ∀ k, MapsTo (fun z ↦ (D.inverse z : X)) (K k).space (C k).chart.source)
    (sigma : P2 × ℝ → (D.sample → ℝ × V3))
    (hsigma : ∀ k : Fin (n + 2), FinitePiecewiseAffineOn sigma
      (signedTubeDiamond ×ˢ Icc (t k.castSucc) (t k.succ)))
    (himage : ∀ k, MapsTo sigma
      (signedTubeDiamond ×ˢ Icc (t k.castSucc) (t k.succ)) (K k).space)
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
    {m : ℕ} (P : Polygon P2 (m + 3)) (hP : P.HasSimplicialEdges)
    (hinjP : Function.Injective P) (hPs : P.boundary ℝ = old.pieces i)
    {L d : ℝ} (hd : 0 < d) (hwidth : 4 * d < L) :
    Nonempty (ComponentReflectionAnnulusData (e := e) (R := R) old i L d) := by
  obtain ⟨hswap, hsign, phi, hPL, hvalue, hwhole, hselected, hclose, hphifib, htrace⟩ :=
    D.exists_self_paired_source_strips hself hcore t ht K hK hKK x y C hKC sigma hsigma himage
      label hcoords closing hfib haxis haxisimage P hP hinjP hPs
  have hab : t 0 < t (Fin.last (n + 2)) := ht (by change 0 < n + 2; omega)
  have hL : 0 < L := by linarith
  let physical : P2 × ℝ → X := fun z => (D.inverse (sigma z) : X)
  let tau := normalizedReflectedTube closing (t 0) (t (Fin.last (n + 2))) L d hab hL hd physical
  obtain ⟨c, hc, hci, hperiod, hmiddle⟩ := exists_reflected_source_annulus_of_cut_strips f
    (fun z => (D.inverse z : X)) sigma closing hswap hsign hab hd hwidth phi hPL
      (fun j z hz => (hvalue j z hz).2.1) hclose hphifib (old.pieces i) hselected
  have hmaps : MapsTo sigma (signedTubeDiamond ×ˢ Icc (t 0) (t (Fin.last (n + 2))))
      D.complex.space := by
    intro z hz
    obtain ⟨k, hk⟩ := ht.monotone.exists_mem_consecutive_Icc hz.2
    exact hKK k (himage k ⟨hz.1, hk⟩)
  have hsource : (⋃ k : Fin (n + 2), signedTubeDiamond ×ˢ Icc (t k.castSucc) (t k.succ)) =
      signedTubeDiamond ×ˢ Icc (t 0) (t (Fin.last (n + 2))) := by
    ext z
    constructor
    · intro hz
      obtain ⟨k, hk⟩ := mem_iUnion.mp hz
      exact ⟨hk.1, (ht.monotone (Fin.zero_le _)).trans hk.2.1,
        hk.2.2.trans (ht.monotone (Fin.le_last _))⟩
    · intro hz
      obtain ⟨k, hk⟩ := ht.monotone.exists_mem_consecutive_Icc hz.2
      exact mem_iUnion.mpr ⟨k, hz.1, hk⟩
  have hsigmaPL : FinitePiecewiseAffineOn sigma
      (signedTubeDiamond ×ˢ Icc (t 0) (t (Fin.last (n + 2)))) :=
    hsource ▸ FinitePiecewiseAffineOn.iUnion hsigma
  have hphysical : PolyhedralPLInCharts e physical
      (signedTubeDiamond ×ˢ Icc (t 0) (t (Fin.last (n + 2)))) := by
    obtain ⟨J, hJ, hJs, hface⟩ := hsigmaPL
    have h := D.inverse_PL.comp_finitePiecewiseAffineOn J hJ ⟨J, hJ, rfl, hface⟩
      (fun z hz => hmaps (hJs.subset hz))
    rwa [hJs] at h
  have hphysicalFib : ∀ z ∈ signedTubeDiamond ×ˢ Icc (t 0) (t (Fin.last (n + 2))),
      ∀ w ∈ signedTubeDiamond ×ˢ Icc (t 0) (t (Fin.last (n + 2))),
      physical z = physical w ↔ z = w ∨
        (z.2 = t 0 ∧ w.2 = t (Fin.last (n + 2)) ∧ closing.linear z.1 = w.1) ∨
        (w.2 = t 0 ∧ z.2 = t (Fin.last (n + 2)) ∧ closing.linear w.1 = z.1) := by
    intro z hz w hw
    have heq : physical z = physical w ↔ sigma z = sigma w := by
      constructor
      · intro h
        exact (D.graph_inverse _ (hmaps hz)).symm.trans
          ((congrArg D.graph h).trans (D.graph_inverse _ (hmaps hw)))
      · exact congrArg (fun q => (D.inverse q : X))
    rw [heq]
    simpa only [Subtype.mk.injEq] using hfib ⟨z, hz⟩ ⟨w, hw⟩
  refine ⟨{
    depth_pos := hd, width_small := hwidth, tube := tau,
    source := ⋃ j, phi j '' (Icc (-1 : ℝ) 1 ×ˢ Icc (t 0) (t (Fin.last (n + 2)))), chart := c,
    tube_PL := normalizedReflectedTube_polyhedralPL e closing (t 0) (t (Fin.last (n + 2)))
      L d hab hL hd physical hphysical,
    tube_fibers := normalizedReflectedTube_fibers closing hswap hsign (t 0)
      (t (Fin.last (n + 2))) L d hab hL hd physical hphysicalFib,
    tube_interior := ?_, source_interior := ?_, chart_PL := hc, chart_inverse_PL := hci,
    period_value := hperiod, full_preimage := ?_, double_trace := htrace, middle := hmiddle }⟩
  · rintro q ⟨z, _hz, rfl⟩
    exact hcore (D.inverse _).property
  · intro w hw
    obtain ⟨j, z, hz, rfl⟩ := mem_iUnion.mp hw
    have hv := hvalue j z hz
    have hint : f (phi j z) ∈ interior R := hv.2.1.symm ▸ hcore (D.inverse _).property
    have hnot : phi j z ∉ frontier S := fun h =>
      disjoint_interior_frontier.notMem_of_mem_left hint ((hfront _ hv.1).mpr h)
    rw [← self_sdiff_frontier]
    exact ⟨hv.1, hnot⟩
  · change S ∩ f ⁻¹' (normalizedReflectedTube closing (t 0) (t (Fin.last (n + 2)))
      L d hab hL hd physical '' singleReflectionTube L d) = _
    rw [normalizedReflectedTube_image]
    exact hwhole

end PoincareConjecture.M76.Dehn.Annuli
