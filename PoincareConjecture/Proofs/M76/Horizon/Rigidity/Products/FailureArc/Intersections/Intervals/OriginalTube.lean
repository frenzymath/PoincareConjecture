import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Intervals.Tubes.CopiedTube

set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli
open PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)
local notation "V3" => (Fin 3 → ℝ)

structure OriginalIntervalTube
    {X ι : Type*} [TopologicalSpace X]
    (e : ι → OpenPartialHomeomorph X V3) (R W : Set X)
    (S T C D : Set P2) (f₀ f₁ : P2 → X) where
  first : P2 → P2
  second : P2 → P2
  map : C3 → X
  first_pl : FinitePiecewiseAffineOn first source
  second_pl : FinitePiecewiseAffineOn second source
  first_embedding : IsEmbedding (fun p : source => first p)
  second_embedding : IsEmbedding (fun p : source => second p)
  first_mapsTo : MapsTo first source S
  second_mapsTo : MapsTo second source T
  pl : PolyhedralPLInCharts e map tube
  embedding : IsEmbedding (fun p : tube => map p)
  mapsTo_region : MapsTo map tube R
  mapsTo_neighborhood : MapsTo map tube W
  first_sheet : ∀ p ∈ source, f₀ (first p) = map (originalStripSheet false p)
  second_sheet : ∀ p ∈ source, f₁ (second p) = map (originalStripSheet true p)
  first_preimage : S ∩ f₀ ⁻¹' (map '' tube) = first '' source
  second_preimage : T ∩ f₁ ⁻¹' (map '' tube) = second '' source
  first_center : first '' arm 0 = C
  second_center : second '' arm 0 = D
  first_trace : ∀ z ∈ tube, map z ∈ f₀ '' S ↔ z.1.2 = z.1.1
  second_trace : ∀ z ∈ tube, map z ∈ f₁ '' T ↔ z.1.2 = -z.1.1
  frontier_iff : ∀ z ∈ tube, map z ∈ frontier R ↔ z.2 = 0 ∨ z.2 = 1

theorem nonempty_originalIntervalTube_of_copied
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R W : Set X}
    {S T C D : Set P2} {f₀ f₁ f : P2 → X}
    (a : P2 ≃ᴬ[ℝ] P2) (hdis : Disjoint S (a '' T))
    (hkeep₀ : EqOn f f₀ S) (hkeep₁ : ∀ x ∈ T, f (a x) = f₁ x)
    (c : Bool → P2 → P2) (τ : C3 → X)
    (hc : ∀ j, FinitePiecewiseAffineOn (c j) source ∧
      IsEmbedding (fun p : source => c j p))
    (hc₀ : MapsTo (c false) source S) (hc₁ : MapsTo (c true) source (a '' T))
    (hτ : PolyhedralPLInCharts e τ tube) (hτi : IsEmbedding (fun z : tube => τ z))
    (hτR : MapsTo τ tube R) (hτW : MapsTo τ tube W)
    (hval : ∀ j p, p ∈ source → f (c j p) = τ (originalStripSheet j p))
    (hpre : (S ∪ a '' T) ∩ f ⁻¹' (τ '' tube) =
      c false '' source ∪ c true '' source)
    (hcenter₀ : c false '' arm 0 = C) (hcenter₁ : c true '' arm 0 = a '' D)
    (hfront : ∀ z ∈ tube, τ z ∈ frontier R ↔ z.2 = 0 ∨ z.2 = 1) :
    Nonempty (OriginalIntervalTube e R W S T C D f₀ f₁) := by
  let sources : Bool → Set P2 := fun j => if j then a '' T else S
  have hmaps : ∀ j, MapsTo (c j) source (sources j) := by
    intro j
    cases j
    · exact hc₀
    · exact hc₁
  have hpres := interval_tube_source_preimages (S := sources) c τ hdis hmaps hval hpre
  have htraces := interval_tube_whole_surface_traces (S := sources) c τ hdis hmaps
    (fun x hx y hy hxy => congrArg Subtype.val (hτi.injective
      (a₁ := ⟨x,hx⟩) (a₂ := ⟨y,hy⟩) hxy)) hval hpre
  obtain ⟨d,hd,hdi,hdT,_,hdval,hdpre,hdcenter⟩ :=
    exists_original_interval_strip_of_translated a (c true) (hc true).1 (hc true).2
      hc₁ hkeep₁ (hpres true) hcenter₁
  have hfirst : f '' S = f₀ '' S := image_congr hkeep₀
  have hsecond : f '' (a '' T) = f₁ '' T := by
    rw [image_image]
    exact image_congr hkeep₁
  refine ⟨{
    first := c false
    second := d
    map := τ
    first_pl := (hc false).1
    second_pl := hd
    first_embedding := (hc false).2
    second_embedding := hdi
    first_mapsTo := hc₀
    second_mapsTo := hdT
    pl := hτ
    embedding := hτi
    mapsTo_region := hτR
    mapsTo_neighborhood := hτW
    first_sheet := fun p hp => (hkeep₀ (hc₀ hp)).symm.trans (hval false p hp)
    second_sheet := fun p hp => (hdval p hp).trans (hval true p hp)
    first_preimage := ?_
    second_preimage := hdpre
    first_center := hcenter₀
    second_center := hdcenter
    first_trace := ?_
    second_trace := ?_
    frontier_iff := hfront }⟩
  · rw [←hpres false]
    ext x
    constructor
    · rintro ⟨hx,hxu⟩
      exact ⟨hx,show f x ∈ τ '' tube from (hkeep₀ hx).symm ▸ hxu⟩
    · rintro ⟨hx,hxu⟩
      exact ⟨hx,show f₀ x ∈ τ '' tube from (hkeep₀ hx) ▸ hxu⟩
  · intro z hz
    simpa only [sources,Bool.false_eq_true,if_false,hfirst] using htraces false z hz
  · intro z hz
    simpa only [sources,if_true,hsecond] using htraces true z hz

end PoincareConjecture.M76.Dehn.Annuli
