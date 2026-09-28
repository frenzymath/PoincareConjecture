import PoincareConjecture.Proofs.M76.Brown.ExceptionalFibers.RegularImageLifting
import PoincareConjecture.Proofs.M76.Brown.ExceptionalFibers.ChartCoreCompression
import PoincareConjecture.Proofs.M76.Brown.ExceptionalFibers.AmbientBallPairTransport
import PoincareConjecture.Proofs.M76.Brown.ExceptionalFibers.CompactSaturatedImage










set_option autoImplicit false

open Set

namespace ContinuousMap

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace X] [T2Space X] [RegularSpace X]





theorem exists_fiber_ballPair_subset (g : C(X, X)) (c : X) (hc : c ∈ range g)
    (hfib : ∀ x y, g x = g y ↔ x = y ∨ (g x = c ∧ g y = c))
    (C : OpenPartialHomeomorph X E) (hCs : C.source = univ) (hCt : C.target = univ)
    (R : OpenPartialHomeomorph X X)
    (hRs : R.source = (g ⁻¹' {c})ᶜ) (hRt : R.target = range g \ {c})
    (hRg : EqOn R g R.source) {Q : Set X} (hQ : IsCompact Q)
    (hpair : IsUnitBallPair E Q (frontier Q))
    (hfQ : g ⁻¹' {c} ⊆ interior Q) (himage : IsOpen (g '' interior Q))
    {U : Set X} (hU : IsOpen U) (hfU : g ⁻¹' {c} ⊆ U) :
    ∃ K : Set X, IsCompact K ∧ g ⁻¹' {c} ⊆ interior K ∧ K ⊆ U ∧
      IsUnitBallPair E K (frontier K) := by
  let U' := U ∩ interior Q
  have hU' : IsOpen U' := hU.inter isOpen_interior
  have hfU' : g ⁻¹' {c} ⊆ U' := fun x hx => ⟨hfU hx, hfQ hx⟩
  have hsat : g ⁻¹' (g '' U') = U' := by
    ext x
    constructor
    · rintro ⟨y, hy, he⟩
      rcases (hfib x y).mp he.symm with hxy | hxy
      · exact hxy.symm ▸ hy
      · exact hfU' hxy.1
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hgU : IsOpen (g '' U') :=
    g.isOpen_image_inside_compact hQ hU' inter_subset_right hsat himage
  have hcgU : c ∈ g '' U' := by
    obtain ⟨x, hx⟩ := hc
    exact ⟨x, hfU' hx, hx⟩
  have hcC : c ∈ C.source := hCs.symm ▸ mem_univ c
  obtain ⟨k, hks, hkt, V, hV, hcV, hkfix⟩ :=
    C.exists_compression_in_chart hCt hcC hgU hcgU
  have hks' : k.source = univ := hks.trans hCs
  have hkW : k.target ⊆ range g := hkt.trans (image_subset_range g U')
  obtain ⟨H, hHs, hHfix, hHg⟩ :=
    R.exists_lift_into_regular_image g.continuous c hRs hRt hRg k hks' hkW hV hcV hkfix
  have hHsmem (x : X) : x ∈ H.source := hHs.symm ▸ mem_univ x
  have hHf {x : X} (hx : x ∈ g ⁻¹' {c}) : H x = x := by
    have hxV : g x ∈ V := by
      change g x = c at hx
      simpa only [hx] using hcV
    exact hHfix hxV
  have hHU (x : X) : H x ∈ U' := by
    have hkm : k (g x) ∈ k.target := k.map_source (hks'.symm ▸ mem_univ (g x))
    have hgm : g (H x) ∈ g '' U' := by rw [hHg]; exact hkt hkm
    have hm : H x ∈ g ⁻¹' (g '' U') := hgm
    rwa [hsat] at hm
  obtain ⟨hK, hKpair⟩ := H.image_compact_ballPair hQ (fun x _ => hHsmem x) hpair
  have hHI : IsOpen (H '' interior Q) :=
    H.isOpen_image_of_subset_source isOpen_interior (fun x _ => hHsmem x)
  have hHK : H '' interior Q ⊆ interior (H '' Q) :=
    interior_maximal (image_mono interior_subset) hHI
  refine ⟨H '' Q, hK, ?_, ?_, hKpair⟩
  · intro x hx
    exact hHK ⟨x, hfQ hx, hHf hx⟩
  · rintro x ⟨y, _, rfl⟩
    exact (hHU y).1

end ContinuousMap
