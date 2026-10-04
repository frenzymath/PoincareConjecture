import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Spheres.HamiltonIndexOneCutSphere
import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Disks.HamiltonIndexOneDiskProduct

/-!
# Regluing the actual cut balls and marked product strips

Extend the complete cut-sphere map over the two actual balls, then glue
to the same strip map on their entire endpoint disks. The whole original
shell-boundary map survives, including its removed band. See Hamilton
1976, p.67 and M76 derivation354.
-/

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareMT.M76.HamiltonIndexOne

local notation "W" => (ℝ × (ℝ × ℝ))
local notation "V" => ((ℝ × ℝ) × ℝ)

/-- The actual cut-ball and product-strip maps reglue to a finite PL
map of the whole index-one shell, retaining the prescribed entire
frontier map. Both endpoint disks use the same values before gluing.
See Hamilton p.67 and derivation354. -/
theorem exists_marked_shell_regluing {B C0 K0 C1 K1 : Set W}
    (hK0 : IsFinitePLBallPair V K0 (frontier K0))
    (hK1 : IsFinitePLBallPair V K1 (frontier K1))
    (hsource : C0 ∪ K0 = squareShell)
    (htarget : C1 ∪ K1 = complementaryRegion B)
    (strip : C0 ≃ₜ C1) (hstrip : strip.IsFinitePL)
    (cut : frontier K0 ≃ₜ frontier K1) (hcut : cut.IsFinitePL)
    (hoverlap : ∀ x : C0, (x : W) ∈ K0 ↔ (strip x : W) ∈ K1)
    (hcontact : C0 ∩ K0 ⊆ frontier K0)
    (hagree : ∀ (x : W) (hxC : x ∈ C0) (hxK : x ∈ K0),
      (strip ⟨x, hxC⟩ : W) = cut ⟨x, hcontact ⟨hxC, hxK⟩⟩)
    (e : frontier squareShell ≃ₜ frontier (complementaryRegion B))
    (hstripBoundary : ∀ (x : frontier squareShell) (hx : (x : W) ∈ C0),
      (strip ⟨x, hx⟩ : W) = e x)
    (hcutBoundary : ∀ (x : frontier squareShell) (hx : (x : W) ∈ frontier K0),
      (cut ⟨x, hx⟩ : W) = e x) :
    ∃ H : squareShell ≃ₜ complementaryRegion B, H.IsFinitePL ∧
      ∀ (x : frontier squareShell) (hx : (x : W) ∈ squareShell),
        (H ⟨x, hx⟩ : W) = e x := by
  obtain ⟨G, hG, hGboundary, _⟩ := hK0.exists_extension hK1 cut hcut
  have hcompat (x : W) (hxC : x ∈ C0) (hxK : x ∈ K0) :
      (strip ⟨x, hxC⟩ : W) = G ⟨x, hxK⟩ := by
    have h := congrArg Subtype.val (hGboundary ⟨x, hcontact ⟨hxC, hxK⟩⟩)
    exact (hagree x hxC hxK).trans h.symm
  obtain ⟨H, hH, hHC, hHK⟩ :=
    Homeomorph.exists_union_finitePL strip G hstrip hG hoverlap hcompat
  let result := (Homeomorph.setCongr hsource.symm).trans
    (H.trans (Homeomorph.setCongr htarget))
  refine ⟨result, hH.setCongr hsource htarget, ?_⟩
  intro x hx
  have hwhole : (x : W) ∈ C0 ∪ K0 := hsource.symm.subset hx
  rcases hwhole with hxC | hxK
  · exact (hHC ⟨x, hxC⟩).trans (hstripBoundary x hxC)
  · have hKS : K0 ⊆ squareShell := subset_union_right.trans hsource.subset
    have hxf : (x : W) ∈ frontier K0 :=
      ⟨subset_closure hxK, fun hi => x.property.2 (interior_mono hKS hi)⟩
    have hGb := congrArg Subtype.val (hGboundary ⟨x, hxf⟩)
    exact (hHK ⟨x, hxK⟩).trans (hGb.trans (hcutBoundary x hxf))

end PoincareMT.M76.HamiltonIndexOne
