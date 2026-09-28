import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.RimBands.Collar.Orientation.Collars.ArmOrientation
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.RimBands.Collar.Orientation.Oriented.PlanarModel
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.RimBands.Collar.SignedArmRescaling

set_option autoImplicit false
open Poincare.Topology.Orientation.ProjectivePlane
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.RimBands
open TubeExterior TubeExterior.CornerBands PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "I" => Icc (0 : ℝ) 1
local notation "J" => Icc (-1 : ℝ) 1

theorem orientation_eq_of_original_signed_arms_of_localOrientation
    {X ι : Type} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (O : LocalOrientation X)
    {e : ι → OpenPartialHomeomorph X V3} {R W Q : Set X}
    {S T C D : Set P2} {f₀ f₁ : P2 → X} {j : V2 → X}
    (he : PLDomain e R)
    (U : OriginalIntervalTube e R W S T C D f₀ f₁) (side : Bool)
    (K : SimplicialComplex ℝ P2) (hK : K.faces.Finite)
    (hKs : K.space = if side then T else S)
    (hf : PolyhedralPLInCharts e (if side then f₁ else f₀) K.space)
    (hi : IsEmbedding (fun z : K.space => (if side then f₁ else f₀) z))
    (hproper : ∀ z ∈ K.space,
      (if side then f₁ else f₀) z ∈ frontier R ↔ z ∈ frontier K.space)
    {r w : ℝ} (hr : 0 < r) (hr1 : r < 1) (hw : 0 < w)
    (P : OriginalDiskProduct e Q j) (hQ : IsClosed Q) (hQR : Q ⊆ R)
    (himage : j '' Disk = (if side then f₁ '' T else f₀ '' S) ∩ Q)
    (o : Bool → Bool)
    (harms : ∀ b t, t ∈ I → ∀ s ∈ J,
      P.map (rimArm b t, s) = prescribedArmBand U r w 0 1 side b (sign (o b) * s, t)) :
    o false = o true := by
  have hsurface : (if side then f₁ else f₀) '' K.space =
      (if side then f₁ '' T else f₀ '' S) := by
    cases side <;> simp_all
  have hz : ((0, 0), (1 / 2 : ℝ)) ∈ tube := by
    norm_num [tube]
  have hcenter : U.map ((0, 0), (1 / 2 : ℝ)) ∈
      (if side then f₁ '' T else f₀ '' S) := by
    cases side
    · exact (U.first_trace _ hz).mpr rfl
    · exact (U.second_trace _ hz).mpr (by norm_num)
  have hnot : U.map ((0, 0), (1 / 2 : ℝ)) ∉ frontier R := by
    rw [U.frontier_iff _ hz]
    norm_num
  have hne : (interior K.space).Nonempty := by
    rw [← hsurface] at hcenter
    obtain ⟨z, hzK, hzval⟩ := hcenter
    refine ⟨z, ?_⟩
    by_contra hn
    exact hnot (hzval ▸ (hproper z hzK).mpr ⟨subset_closure hzK, hn⟩)
  have hex :=
    exists_original_proper_planar_pair_surface_cooriented_charts_of_localOrientation
      O e he.cover he.compatible K hK (if side then f₁ else f₀)
      hf hi hne R hproper
  rw [hsurface] at hex
  obtain ⟨E, hcover, hpair, hcompat⟩ := hex
  exact orientation_eq_of_actual_signed_arms U side hr hr1 hw P hQ hQR himage o harms
    E (fun x hx => ⟨⟨x, hx⟩, hcover ⟨x, hx⟩⟩) hpair hcompat

theorem orientation_eq_of_original_band_arms_of_localOrientation
    {X ι : Type} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (O : LocalOrientation X)
    {e : ι → OpenPartialHomeomorph X V3} {R W Q : Set X}
    {S T C D : Set P2} {f₀ f₁ : P2 → X} {j : V2 → X}
    (he : PLDomain e R)
    (U : OriginalIntervalTube e R W S T C D f₀ f₁) (side : Bool)
    (K : SimplicialComplex ℝ P2) (hK : K.faces.Finite)
    (hKs : K.space = if side then T else S)
    (hf : PolyhedralPLInCharts e (if side then f₁ else f₀) K.space)
    (hi : IsEmbedding (fun z : K.space => (if side then f₁ else f₀) z))
    (hproper : ∀ z ∈ K.space,
      (if side then f₁ else f₀) z ∈ frontier R ↔ z ∈ frontier K.space)
    {r ρ w : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hρ : 0 < ρ) (hw : 0 < w) (hwρ : w / ρ ≤ 1)
    (P : OriginalDiskProduct e Q j) (hQ : IsClosed Q) (hQR : Q ⊆ R)
    (himage : j '' Disk = (if side then f₁ '' T else f₀ '' S) ∩ Q)
    (F : V2 × ℝ → X) (o : Bool → Bool)
    (hmark : ∀ z ∈ Rim, ∀ s ∈ J, P.map (z, s) = F (z, (w / ρ) * s))
    (harms : ∀ b t, t ∈ I → ∀ s ∈ J,
      F (rimArm b t, s) = prescribedArmBand U r ρ 0 1 side b (sign (o b) * s, t)) :
    o false = o true := by
  exact orientation_eq_of_original_signed_arms_of_localOrientation O he U side K hK hKs hf hi hproper
    hr hr1 hw P hQ hQR himage o
    (signed_arms_common_width U P F r side o hρ hw hwρ hmark harms)

end PoincareConjecture.M76.Dehn.Annuli.RimBands
