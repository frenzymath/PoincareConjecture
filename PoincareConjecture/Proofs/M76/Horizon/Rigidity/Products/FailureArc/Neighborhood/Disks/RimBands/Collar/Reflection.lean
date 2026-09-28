import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.RimBands.Collar.Rescaling
import PoincareConjecture.Proofs.M76.Rigidity.OriginalProductRescaling

set_option autoImplicit false

open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.RimBands
open TubeExterior TubeExterior.CornerBands

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "E" => (V2 × ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1
local notation "J" => Icc (0 : ℝ) 1

theorem bandTimeScale_sign_involutive (o : Bool) :
    Function.Involutive (bandTimeScale (sign o)) := by
  intro p
  simp only [bandTimeScale_apply, sign_mul_sign]

theorem bandTimeScale_sign_mem_Icc (o : Bool) (B : Set V2) (a : ℝ) (p : E) :
    bandTimeScale (sign o) p ∈ B ×ˢ Icc (-a) a ↔ p ∈ B ×ˢ Icc (-a) a := by
  cases o <;> simp [sign, bandTimeScale_apply, neg_le, and_comm]

theorem bandTimeScale_sign_mem_Ioo (o : Bool) (B : Set V2) (a : ℝ) (p : E) :
    bandTimeScale (sign o) p ∈ B ×ˢ Ioo (-a) a ↔ p ∈ B ×ˢ Ioo (-a) a := by
  cases o <;> simp [sign, bandTimeScale_apply, neg_lt, and_comm]

theorem bandTimeScale_sign_closed_image (o : Bool) (B : Set V2) (a : ℝ) :
    bandTimeScale (sign o) '' (B ×ˢ Icc (-a) a) = B ×ˢ Icc (-a) a := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact (bandTimeScale_sign_mem_Icc o B a q).mpr hq
  · intro hp
    exact ⟨_, (bandTimeScale_sign_mem_Icc o B a p).mpr hp,
      bandTimeScale_sign_involutive o p⟩

theorem bandTimeScale_sign_open_image (o : Bool) (B : Set V2) (a : ℝ) :
    bandTimeScale (sign o) '' (B ×ˢ Ioo (-a) a) = B ×ˢ Ioo (-a) a := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact (bandTimeScale_sign_mem_Ioo o B a q).mpr hq
  · intro hp
    exact ⟨_, (bandTimeScale_sign_mem_Ioo o B a p).mpr hp,
      bandTimeScale_sign_involutive o p⟩

theorem reflected_boundary_band_properties
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {Q : Set X} {j : V2 → X}
    {F : E → X} (hF : PolyhedralPLInCharts e F (Rim ×ˢ I))
    (hi : InjOn F (Rim ×ˢ I)) (hQ : MapsTo F (Rim ×ˢ I) (frontier Q))
    (hc : ∀ z ∈ Rim, F (z, 0) = j z)
    (ho : IsOpen ((Subtype.val : frontier Q → X) ⁻¹' (F '' (Rim ×ˢ Ioo (-1 : ℝ) 1))))
    (o : Bool) :
    PolyhedralPLInCharts e (F ∘ bandTimeScale (sign o)) (Rim ×ˢ I) ∧
      InjOn (F ∘ bandTimeScale (sign o)) (Rim ×ˢ I) ∧
      MapsTo (F ∘ bandTimeScale (sign o)) (Rim ×ˢ I) (frontier Q) ∧
      (∀ z ∈ Rim, (F ∘ bandTimeScale (sign o)) (z, 0) = j z) ∧
      IsOpen ((Subtype.val : frontier Q → X) ⁻¹'
        ((F ∘ bandTimeScale (sign o)) '' (Rim ×ˢ Ioo (-1 : ℝ) 1))) := by
  have hmap : MapsTo (bandTimeScale (sign o)) (Rim ×ˢ I) (Rim ×ˢ I) :=
    fun p hp => (bandTimeScale_sign_mem_Icc o Rim 1 p).mpr hp
  obtain ⟨K, hK, hKs⟩ := exists_finite_hamiltonMeridianBand (show (-1 : ℝ) < 1 by norm_num)
  have hscale : FinitePiecewiseAffineOn (bandTimeScale (sign o)) K.space :=
    ⟨K, hK, rfl, K.affineOnFaces_affine _⟩
  refine ⟨?_, ?_, hQ.comp hmap, ?_, ?_⟩
  · have h := hF.comp_finitePiecewiseAffineOn K hK hscale
      (fun _ hp => hmap (hKs.subset hp))
    exact hKs ▸ h
  · intro p hp q hq heq
    exact (bandTimeScale_sign_involutive o).injective (hi (hmap hp) (hmap hq) heq)
  · intro z hz
    simpa using hc z hz
  · rwa [image_comp, bandTimeScale_sign_open_image]

theorem reflected_boundary_band_arms
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R W : Set X}
    {S T C D : Set P2} {f₀ f₁ : P2 → X}
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    {F : E → X} {r ρ t₀ t₁ : ℝ} {side : Bool} (o : Bool → Bool)
    (hcoherent : o false = o true)
    (harms : ∀ b t, t ∈ J → ∀ s ∈ I,
      F (rimArm b t, s) = prescribedArmBand U r ρ t₀ t₁ side b (sign (o b) * s, t)) :
    ∀ b t, t ∈ J → ∀ s ∈ I,
      (F ∘ bandTimeScale (sign (o false))) (rimArm b t, s) =
        prescribedArmBand U r ρ t₀ t₁ side b (s, t) := by
  have hequal (b : Bool) : o b = o false := by
    cases b
    · rfl
    · exact hcoherent.symm
  intro b t ht s hs
  have hsigned : sign (o false) * s ∈ I := by
    have h := (bandTimeScale_sign_mem_Icc (o false) univ 1 ((0 : V2), s)).mpr ⟨trivial, hs⟩
    exact h.2
  change F (rimArm b t, sign (o false) * s) = _
  rw [harms b t ht _ hsigned, hequal b, sign_mul_sign]

theorem reflected_boundary_band_lateral
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R W : Set X}
    {S T C D : Set P2} {f₀ f₁ : P2 → X}
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    {F : E → X} {r : ℝ} (o : Bool)
    (hlateral : ∀ z ∈ Rim, ∀ s ∈ I,
      F (z, s) ∈ U.map '' lateral r ↔ ∃ b : Bool, ∃ t ∈ J, z = rimArm b t) :
    ∀ z ∈ Rim, ∀ s ∈ I,
      (F ∘ bandTimeScale (sign o)) (z, s) ∈ U.map '' lateral r ↔
        ∃ b : Bool, ∃ t ∈ J, z = rimArm b t := by
  intro z hz s hs
  exact hlateral z hz (sign o * s)
    ((bandTimeScale_sign_mem_Icc o Rim 1 (z, s)).mpr ⟨hz, hs⟩).2

theorem exists_reflected_original_disk_product
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e R j) (o : Bool) :
    ∃ Q : OriginalDiskProduct e R j,
      Q.map = P.map ∘ bandTimeScale (sign o) ∧
      (∀ a : ℝ, Q.map '' (Disk ×ˢ Icc (-a) a) = P.map '' (Disk ×ˢ Icc (-a) a)) ∧
      ∀ a : ℝ, Q.map '' (Disk ×ˢ Ioo (-a) a) = P.map '' (Disk ×ˢ Ioo (-a) a) := by
  have hmap : MapsTo (bandTimeScale (sign o)) (Disk ×ˢ I) (Disk ×ˢ I) :=
    fun p hp => (bandTimeScale_sign_mem_Icc o Disk 1 p).mpr hp
  have hball := (isFinitePLBallPair_unit_cube (ι := Fin 2)).prod
    (isFinitePLBallPair_Icc (show (-1 : ℝ) < 1 by norm_num))
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := hball
  have hscale : FinitePiecewiseAffineOn (bandTimeScale (sign o)) K.space :=
    ⟨K, hK, rfl, K.affineOnFaces_affine _⟩
  have hPL : PolyhedralPLInCharts e (P.map ∘ bandTimeScale (sign o)) (Disk ×ˢ I) := by
    have h := P.polyhedral.comp_finitePiecewiseAffineOn K hK hscale
      (fun _ hp => hmap (hKs.subset hp))
    exact hKs ▸ h
  have hi : InjOn (P.map ∘ bandTimeScale (sign o)) (Disk ×ˢ I) := by
    intro x hx y hy hxy
    exact (bandTimeScale_sign_involutive o).injective (P.injective (hmap hx) (hmap hy) hxy)
  let : CompactSpace (Disk ×ˢ I : Set E) :=
    isCompact_iff_compactSpace.mp ((isCompact_closedBall (0 : V2) 1).prod isCompact_Icc)
  let Q : OriginalDiskProduct e R j := {
    map := P.map ∘ bandTimeScale (sign o)
    polyhedral := hPL
    injective := hi
    embedding := hPL.continuousOn.domRestrict.isClosedEmbedding
      (fun x y hxy => Subtype.ext (hi x.property y.property hxy))
    inside := P.inside.comp hmap
    central := by
      intro z hz
      simpa using P.central z hz
    proper := fun x hx => P.proper (bandTimeScale (sign o) x) (hmap hx) }
  refine ⟨Q, rfl, ?_, ?_⟩
  · intro a
    exact (image_comp P.map (bandTimeScale (sign o)) _).trans
      (congrArg (image P.map) (bandTimeScale_sign_closed_image o Disk a))
  · intro a
    exact (image_comp P.map (bandTimeScale (sign o)) _).trans
      (congrArg (image P.map) (bandTimeScale_sign_open_image o Disk a))

end PoincareConjecture.M76.Dehn.Annuli.RimBands
