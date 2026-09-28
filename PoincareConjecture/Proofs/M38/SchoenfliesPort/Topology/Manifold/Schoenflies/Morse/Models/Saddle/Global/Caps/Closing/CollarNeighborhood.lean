import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.TerminalAnnuli

open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.Poincare.Manifold.Schoenflies.Saddle
open _root_.PoincareConjecture

namespace M38Schoenflies

noncomputable section
set_option autoImplicit false

open Set Metric Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

theorem exists_surface_neighborhood_in_chart
    {s : S2 → E3} (hs : Topology.IsEmbedding s)
    (m : OpenPartialHomeomorph E2 S2) {V : Set E2} (hV : IsOpen V)
    (hVm : V ⊆ m.source) :
    ∃ U : Set E3, IsOpen U ∧ (s ∘ m) '' V ⊆ U ∧
      range s ∩ U ⊆ (s ∘ m) '' V := by
  obtain ⟨U, hU, heq⟩ := hs.isInducing.isOpen_iff.mp
    (m.isOpen_image_of_subset_source hV hVm)
  refine ⟨U, hU, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    change m x ∈ s ⁻¹' U
    rw [heq]
    exact mem_image_of_mem m hx
  · rintro _ ⟨⟨q, rfl⟩, hq⟩
    have hqm : q ∈ m '' V := by rw [← heq]; exact hq
    obtain ⟨x, hx, rfl⟩ := hqm
    exact mem_image_of_mem (s ∘ m) hx

theorem exists_common_surface_neighborhood_of_eqOn_charts
    {s t : S2 → E3} (hs : Topology.IsEmbedding s) (ht : Topology.IsEmbedding t)
    (m n : OpenPartialHomeomorph E2 S2) {V : Set E2} (hV : IsOpen V)
    (hVm : V ⊆ m.source) (hVn : V ⊆ n.source)
    (heq : EqOn (s ∘ m) (t ∘ n) V) :
    ∃ U : Set E3, IsOpen U ∧ (s ∘ m) '' V ⊆ U ∧
      range s ∩ U = range t ∩ U := by
  obtain ⟨A, hA, hVA, hcoverA⟩ := exists_surface_neighborhood_in_chart hs m hV hVm
  obtain ⟨B, hB, hVB, hcoverB⟩ := exists_surface_neighborhood_in_chart ht n hV hVn
  have himage : (s ∘ m) '' V = (t ∘ n) '' V := image_congr heq
  refine ⟨A ∩ B, hA.inter hB, subset_inter hVA (himage ▸ hVB), ?_⟩
  ext y
  constructor
  · rintro ⟨hy, hU⟩
    obtain ⟨x, hx, hxy⟩ := himage ▸ hcoverA ⟨hy, hU.1⟩
    exact ⟨⟨n x, hxy⟩, hU⟩
  · rintro ⟨hy, hU⟩
    obtain ⟨x, hx, hxy⟩ := himage.symm ▸ hcoverB ⟨hy, hU.2⟩
    exact ⟨⟨m x, hxy⟩, hU⟩

theorem exists_band_neighborhood_in_outer_annulus
    {s : S2 → E3} (hs : Topology.IsEmbedding s)
    (m : OpenPartialHomeomorph E2 S2) {r : Real} (hr : 1 < r)
    (hsource : closedBall 0 r ⊆ m.source)
    {W : Set E3} (hW : W ⊆ range s)
    (hdis : Disjoint ((s ∘ m) '' ball (0 : E2) 1) W) :
    ∃ U : Set E3, IsOpen U ∧ (s ∘ m) '' sphere (0 : E2) 1 ⊆ U ∧
      W ∩ U ⊆ (s ∘ m) '' (closedBall (0 : E2) r \ ball 0 1) := by
  have hopen : IsOpen (m '' ball (0 : E2) r) :=
    m.isOpen_image_of_subset_source isOpen_ball (ball_subset_closedBall.trans hsource)
  obtain ⟨U, hU, heq⟩ := hs.isInducing.isOpen_iff.mp hopen
  refine ⟨U, hU, ?_, ?_⟩
  · rintro y ⟨x, hx, rfl⟩
    change m x ∈ s ⁻¹' U
    rw [heq]
    exact mem_image_of_mem m (closedBall_subset_ball hr (sphere_subset_closedBall hx))
  · rintro y ⟨hyW, hyU⟩
    obtain ⟨q, rfl⟩ := hW hyW
    have hq : q ∈ m '' ball (0 : E2) r := by rw [← heq]; exact hyU
    obtain ⟨x, hx, rfl⟩ := hq
    refine ⟨x, ⟨ball_subset_closedBall hx, ?_⟩, rfl⟩
    intro hxunit
    exact disjoint_left.mp hdis (mem_image_of_mem (s ∘ m) hxunit) hyW

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

end

end M38Schoenflies
