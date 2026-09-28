import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Boundary.Upper.Extension.ComponentModel
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Boundary.Upper.Extension.TrackTransport
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Boundary.Upper.Extension.ClopenTrack
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Collars.OriginalRegionMotion
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.General.PLDomainInteriorConnected

set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76
local notation "I" => unitInterval
local notation "V3" => (Fin 3 → ℝ)

theorem PLDomain.exists_original_boundary_component_motion
    {E X ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R S : Set X}
    (he : PLDomain e R) (hR : IsCompact R) (hconn : IsConnected R)
    (hSB : S ⊆ frontier R) (hS : IsClopen ((Subtype.val : frontier R → X) ⁻¹' S))
    (A : SimplicialComplex ℝ E) (hA : A.faces.Finite)
    (F : E → X) (hF : PolyhedralPLInCharts e F A.space)
    (H : A.space ≃ₜ S) (hFval : ∀ x : A.space, F x = (H x : X))
    (G : I → A.space ≃ₜ A.space)
    (hG : Continuous (fun z : I × A.space => G z.1 z.2))
    (hGi : Continuous (fun z : I × A.space => (G z.1).symm z.2))
    (hG0 : G 0 = Homeomorph.refl A.space)
    (track : ℝ × E → E)
    (htrack : FinitePiecewiseAffineOn track (Icc (0 : ℝ) 1 ×ˢ A.space))
    (hvalue : ∀ t : I, ∀ x : A.space, track ((t : ℝ), x) = (G t x : E)) :
    ∃ M : I → R ≃ₜ R,
      Continuous (fun z : I × R => M z.1 z.2) ∧
      Continuous (fun z : I × R => (M z.1).symm z.2) ∧
      M 0 = Homeomorph.refl R ∧
      (∀ t, ChartwisePLHomeomorph e e (M t)) ∧
      (∀ t (x : A.space),
        (M t ⟨H x, he.closed.frontier_subset (hSB (H x).property)⟩ : X) = H (G t x)) ∧
      (∀ t (x : R), (x : X) ∈ frontier R → (x : X) ∉ S → M t x = x) ∧
      ∀ t (x : R), (M t x : X) ∈ frontier R ↔ (x : X) ∈ frontier R := by
  obtain ⟨s, K, HB, c, delta, hK, hd, _, hc, hci, _, _, hb, extend⟩ :=
    CollarIsotopy.exists_prepared_original_boundary_collar_motion he hR
      (he.isConnected_interior hconn).nonempty isOpen_univ (subset_univ _)
  have hcinj : InjOn c (K.space ×ˢ Icc (0 : ℝ) delta) := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (hci.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)
  obtain ⟨L, Q, hL, hLK, hQ, hQval, hclopen, hmark⟩ :=
    exists_finitePL_component_in_collar_base he.compatible hSB hS HB hd.le c hc hcinj hb
      A hA F hF H hFval
  obtain ⟨G₁, track₁, hc₁, hci₁, hzero₁, htrack₁, hvalue₁, hconj⟩ :=
    exists_finitePL_conjugate_track hL Q hQ G hG hGi hG0 track htrack hvalue
  obtain ⟨G₂, track₂, hc₂, hci₂, hzero₂, htrack₂, hvalue₂, hon, hoff⟩ :=
    exists_finitePL_clopen_track_extension hK hL hLK hclopen G₁ hc₁ hci₁ hzero₁
      track₁ htrack₁ hvalue₁
  obtain ⟨M, hMc, hMci, hM0, hMPL, houter, _, _, _⟩ :=
    extend G₂ hc₂ hci₂ (fun x => by rw [hzero₂]; rfl) track₂ htrack₂ hvalue₂
  have hQbase (x : A.space) : (HB ⟨Q x, hLK (Q x).property⟩ : X) = H x :=
    (hb ⟨Q x, hLK (Q x).property⟩).symm.trans (hQval x)
  have hMmark (t : I) (x : A.space) :
      (M t ⟨H x, he.closed.frontier_subset (hSB (H x).property)⟩ : X) = H (G t x) := by
    have hinput : (⟨HB ⟨Q x, hLK (Q x).property⟩,
        he.closed.frontier_subset (HB ⟨Q x, hLK (Q x).property⟩).property⟩ : R) =
        ⟨H x, he.closed.frontier_subset (hSB (H x).property)⟩ := Subtype.ext (hQbase x)
    rw [← hinput, houter]
    have hmotion : G₂ t ⟨Q x, hLK (Q x).property⟩ =
        (⟨Q (G t x), hLK (Q (G t x)).property⟩ : K.space) := by
      apply Subtype.ext
      exact (hon t (Q x)).trans (congrArg Subtype.val (hconj t x))
    rw [hmotion]
    exact hQbase (G t x)
  have hMout (t : I) (x : R) (hx : (x : X) ∈ frontier R) (hxS : (x : X) ∉ S) :
      M t x = x := by
    let z : K.space := HB.symm ⟨x, hx⟩
    have hzval : (HB z : X) = x := congrArg Subtype.val (HB.apply_symm_apply ⟨x, hx⟩)
    have hzout : (z : s → ℝ × V3) ∉ L.space := by
      intro hz
      exact hxS (hzval ▸ (hmark z).mp hz)
    apply Subtype.ext
    have hinput : (⟨HB z, he.closed.frontier_subset (HB z).property⟩ : R) = x :=
      Subtype.ext hzval
    rw [← hinput, houter, hoff t z hzout]
  refine ⟨M, hMc, hMci, hM0, hMPL, hMmark, hMout, ?_⟩
  intro t x
  constructor
  · intro hx
    let z : K.space := (G₂ t).symm (HB.symm ⟨M t x, hx⟩)
    have hMx : (M t ⟨HB z, he.closed.frontier_subset (HB z).property⟩ : X) = M t x := by
      rw [houter]
      change (HB (G₂ t ((G₂ t).symm (HB.symm ⟨M t x, hx⟩))) : X) = M t x
      rw [(G₂ t).apply_symm_apply, HB.apply_symm_apply]
    have hxval := congrArg Subtype.val ((M t).injective (Subtype.ext hMx))
    exact hxval ▸ (HB z).property
  · intro hx
    let z : K.space := HB.symm ⟨x, hx⟩
    have hzval : (HB z : X) = x := congrArg Subtype.val (HB.apply_symm_apply ⟨x, hx⟩)
    have hinput : (⟨HB z, he.closed.frontier_subset (HB z).property⟩ : R) = x :=
      Subtype.ext hzval
    rw [← hinput, houter]
    exact (HB (G₂ t z)).property

end PoincareConjecture.M76
