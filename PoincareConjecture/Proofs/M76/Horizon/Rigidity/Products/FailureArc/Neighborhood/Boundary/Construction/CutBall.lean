import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Boundary.Construction.PanelSphere
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Boundary.Assembly.Frontier
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Boundary.SelectedFilling
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Exhaustion.TubeDiskAttachment
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Irreducibility.TubeExterior
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.Matching.SuccessiveCuts
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Construction.CutIrreducibility

set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.BoundaryAssembly
open TubeExterior TubeExterior.CornerBands RimBands PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "I" => Icc (0 : ℝ) 1
local notation "J" => Icc (-1 : ℝ) 1

theorem nonempty_original_ball_of_marked_disk_products
    {X ι E₀ E₁ : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀]
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    {e : ι → OpenPartialHomeomorph X V3} {R W : Set X}
    {S T C D : Set P2} {f₀ f₁ : P2 → X}
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    (hR : IsCompact R) (hI : IsPLIrreducible e R) (hconn : IsPreconnected R)
    {r w : ℝ} (hw : 0 < w) (hr1 : r < 1)
    {j : Bool → V2 → X}
    (P : ∀ b, OriginalDiskProduct e (R \ U.map '' openTube r) (j b))
    (F : Bool → V2 × ℝ → X) (ρ : Bool → ℝ)
    (hρ : ∀ b, 0 < ρ b) (hρr : ∀ b, ρ b < r) (hwρ : ∀ b, w/ρ b ≤ 1)
    (hmark : ∀ b, ∀ z ∈ Rim, ∀ s ∈ J,
      (P b).map (z,s) = F b (z,(w/ρ b)*s))
    (harms : ∀ side b : Bool, ∀ t ∈ I, ∀ s ∈ J,
      F side (rimArmPoint b t,s) = prescribedArmBand U r (ρ side) 0 1 side b (s,t))
    (hlateral : ∀ side, ∀ z ∈ Rim, ∀ s ∈ J,
      F side (z,s) ∈ U.map '' lateral r ↔ ∃ b : Bool, ∃ t ∈ I, z = rimArmPoint b t)
    (hdis : Disjoint ((P false).map '' (Disk ×ˢ J)) ((P true).map '' (Disk ×ˢ J)))
    (hopen : ∀ b, ∀ v : ℝ, 0 < v → v ≤ 1 →
      IsOpen ((Subtype.val : ↥(R \ U.map '' openTube r) → X) ⁻¹'
        ((P b).map '' (Disk ×ˢ Ioo (-v) v))))
    {g₀ : E₀ → X} {g₁ : E₁ → X} {c₀ q₀ : Set E₀} {c₁ q₁ : Set E₁}
    (hc₀ : IsFinitePLBallPair P2 c₀ q₀) (hc₁ : IsFinitePLBallPair P2 c₁ q₁)
    (hg₀ : PolyhedralPLInCharts e g₀ c₀) (hg₁ : PolyhedralPLInCharts e g₁ c₁)
    (hi₀ : InjOn g₀ c₀) (hi₁ : InjOn g₁ c₁)
    (hrim₀ : (⋃ i, panelFamily U (P false) (P true) r w i '' (I ×ˢ {0})) = g₀ '' q₀)
    (hrim₁ : (⋃ i, panelFamily U (P false) (P true) r w i '' (I ×ˢ {1})) = g₁ '' q₁)
    (hcontact₀ : ((⋃ i : Bool × Bool, U.map '' panel r (w/2) i) ∪
      ((P false).endDisks ∪ (P true).endDisks)) ∩ (g₀ '' c₀) = g₀ '' q₀)
    (hcontact₁ : ((⋃ i : Bool × Bool, U.map '' panel r (w/2) i) ∪
      ((P false).endDisks ∪ (P true).endDisks)) ∩ (g₁ '' c₁) = g₁ '' q₁)
    (hgdis : Disjoint (g₀ '' c₀) (g₁ '' c₁))
    (hold₀ : g₀ '' c₀ ⊆ frontier R \
      (U.map '' openTube r ∪ (P false).openStrip ∪ (P true).openStrip))
    (hold₁ : g₁ '' c₁ ⊆ frontier R \
      (U.map '' openTube r ∪ (P false).openStrip ∪ (P true).openStrip)) :
    let B := ((⋃ i : Bool × Bool, U.map '' panel r (w/2) i) ∪
      ((P false).endDisks ∪ (P true).endDisks)) ∪ ((g₀ '' c₀) ∪ (g₁ '' c₁))
    ∃ Q₁ : OriginalDiskProduct e (P false).cutCarrier (j true),
      Q₁.map = (P true).map ∧
      Q₁.cutCarrier = R \ (U.map '' openTube r ∪ (P false).openStrip ∪ (P true).openStrip) ∧
      IsCompact Q₁.cutCarrier ∧ IsPLIrreducible e Q₁.cutCarrier ∧
      frontier Q₁.cutCarrier = B ∧ Nonempty (ChartwisePLBall e Q₁.cutCarrier B) := by
  dsimp only
  have hr : 0 < r := (hρ false).trans (hρr false)
  have hQ := TubeExterior.OriginalIntervalTube.isCompact_exterior U hR hI.1 hr hr1.le
  have hIQ := TubeExterior.OriginalIntervalTube.isPLIrreducible_exterior U hR hI hr hr1
  have hopen₀ : IsOpen ((Subtype.val : ↥(R \ U.map '' openTube r) → X) ⁻¹'
      (P false).openStrip) := hopen false (1/2) (by norm_num) (by norm_num)
  obtain ⟨Q₁,hmap,he₀,hc₀cut,he₁,hc₁cut,hcutdis,hopen₁,hfront₁,hoverlap₁,hcover₁,hne⟩ :=
    exists_unchanged_product_in_disjoint_cut (P false) (P true) hQ hIQ.1 hopen₀ hdis (hopen true)
  have hI₀ := (P false).isPLIrreducible_cut_of_isCompact hQ hc₀cut hIQ
  have hI₁ := Q₁.isPLIrreducible_cut_of_isCompact hc₀cut hc₁cut hI₀
  have hopenEq : Q₁.openStrip = (P true).openStrip := by
    unfold OriginalDiskProduct.openStrip
    rw [hmap]
  have hendEq : Q₁.endDisks = (P true).endDisks := by
    unfold OriginalDiskProduct.endDisks
    rw [hmap]
  have hclosedDis : Disjoint (P false).closedStrip (P true).closedStrip := by
    simpa only [OriginalDiskProduct.closedStrip,hmap] using hcutdis
  obtain ⟨sph⟩ := nonempty_original_sphere_of_marked_disk_products U hR hI.1 hw hr1.le
    P F ρ hρ hρr hwρ hmark harms hlateral hclosedDis hc₀ hc₁ hg₀ hg₁ hi₀ hi₁
    hrim₀ hrim₁ hcontact₀ hcontact₁ hgdis
  obtain ⟨hfront,hcarrier⟩ := final_frontier_of_marked_products U hR hI.1 hw hr1.le
    P F ρ hρ hρr hwρ hmark harms hlateral Q₁ hmap hcutdis hopen₀ hopen₁
  have hSfront : ((⋃ i : Bool × Bool, U.map '' panel r (w/2) i) ∪
      ((P false).endDisks ∪ (P true).endDisks)) ∪ ((g₀ '' c₀) ∪ (g₁ '' c₁)) ⊆
      frontier Q₁.cutCarrier := by
    rw [hfront]
    exact union_subset subset_union_right
      ((union_subset hold₀ hold₁).trans subset_union_left)
  obtain ⟨x,hx⟩ := sph.isConnected.nonempty
  obtain ⟨_,_,_,_,hSP,_,hcompfront,_,hball,_⟩ :=
    nonempty_original_ball_of_boundary_sphere hc₁cut hI₁ hSfront sph x hx
  have hxcut : x ∈ Q₁.cutCarrier := hI₁.1.closed.frontier_subset (hSfront hx)
  have hlat : U.map '' lateral r \ ((P false).openStrip ∪ Q₁.openStrip) ⊆
      connectedComponentIn Q₁.cutCarrier x := by
    rw [hopenEq,lateral_sdiff_two_openStrips U hR hI.1 hw hr1.le P F ρ hρ hρr
      hwρ hmark harms hlateral]
    exact (subset_union_left.trans subset_union_left).trans hSP
  have hend : (P false).endDisks ∪ Q₁.endDisks ⊆ connectedComponentIn Q₁.cutCarrier x := by
    rw [hendEq]
    exact (subset_union_right.trans subset_union_left).trans hSP
  have hwhole := final_cut_component_eq_of_attachment_faces U hR hI.1 hconn hr hr1.le
    (P false) Q₁ hcutdis hopen₀ hopen₁ he₁ hxcut hlat hend
  rw [hwhole] at hcompfront hball
  exact ⟨Q₁,hmap,hcarrier,hc₁cut,hI₁,hcompfront,hball⟩

end PoincareConjecture.M76.Dehn.Annuli.BoundaryAssembly
