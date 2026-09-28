import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.MarkedRectangle
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.NestedFiniteCoordinateCubes

set_option autoImplicit false
noncomputable section
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.CubeCoordinates

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "I" => Icc (0 : ℝ) 1
local notation "Rect" => (I ×ˢ I : Set P2)

def toRectangle : V2 →ᴬ[ℝ] P2 :=
  ((1 / 2 : ℝ) • ((ContinuousLinearMap.proj (0 : Fin 2) : V2 →L[ℝ] ℝ).toContinuousAffineMap +
    ContinuousAffineMap.const ℝ V2 (1 : ℝ))).prod
  ((1 / 2 : ℝ) • ((ContinuousLinearMap.proj (1 : Fin 2) : V2 →L[ℝ] ℝ).toContinuousAffineMap +
    ContinuousAffineMap.const ℝ V2 (1 : ℝ)))

@[simp] theorem toRectangle_apply (z : V2) :
    toRectangle z = ((z 0 + 1) / 2,(z 1 + 1) / 2) := by
  simp [toRectangle,div_eq_mul_inv,mul_comm,mul_add]

def fromRectangle (p : P2) : V2 := ![2*p.1-1,2*p.2-1]

@[simp] theorem fromRectangle_toRectangle (z : V2) :
    fromRectangle (toRectangle z) = z := by
  funext i
  fin_cases i <;> simp [fromRectangle] <;> ring

@[simp] theorem toRectangle_fromRectangle (p : P2) :
    toRectangle (fromRectangle p) = p := by
  apply Prod.ext <;> simp [fromRectangle]

def homeomorph : V2 ≃ₜ P2 where
  toFun := toRectangle
  invFun := fromRectangle
  left_inv := fromRectangle_toRectangle
  right_inv := toRectangle_fromRectangle
  continuous_toFun := toRectangle.continuous
  continuous_invFun := by
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp [fromRectangle] <;> fun_prop

theorem mem_disk_iff (z : V2) : z ∈ Disk ↔
    z 0 ∈ Icc (-1 : ℝ) 1 ∧ z 1 ∈ Icc (-1 : ℝ) 1 := by
  rw [closedBall_pi _ zero_le_one]
  simp only [mem_pi,mem_univ,forall_true_left,Pi.zero_apply,Real.closedBall_eq_Icc,
    zero_sub,zero_add]
  constructor
  · intro h; exact ⟨h 0,h 1⟩
  · rintro ⟨h0,h1⟩ i
    fin_cases i
    · exact h0
    · exact h1

theorem toRectangle_mem_iff (z : V2) : toRectangle z ∈ Rect ↔ z ∈ Disk := by
  rw [toRectangle_apply,mem_disk_iff]
  simp only [mem_prod,mem_Icc]
  constructor <;> rintro ⟨⟨h0,h1⟩,⟨h2,h3⟩⟩ <;>
    constructor <;> constructor <;> linarith

theorem toRectangle_bijOn : BijOn toRectangle Disk Rect := by
  refine ⟨fun z hz => (toRectangle_mem_iff z).mpr hz,homeomorph.injective.injOn,?_⟩
  intro p hp
  refine ⟨fromRectangle p,?_,toRectangle_fromRectangle p⟩
  exact (toRectangle_mem_iff _).mp ((toRectangle_fromRectangle p).symm ▸ hp)

theorem toRectangle_image : toRectangle '' Disk = Rect := toRectangle_bijOn.image_eq

theorem toRectangle_rim_image : toRectangle '' Rim = frontier Rect := by
  have h := homeomorph.image_frontier Disk
  change toRectangle '' frontier Disk = frontier (toRectangle '' Disk) at h
  rwa [frontier_closedBall _ one_ne_zero,toRectangle_image] at h

theorem toRectangle_rim_iff (z : V2) : toRectangle z ∈ frontier Rect ↔ z ∈ Rim := by
  rw [← toRectangle_rim_image]
  exact homeomorph.injective.mem_set_image

theorem toRectangle_finitePL : FinitePiecewiseAffineOn toRectangle Disk := by
  obtain ⟨K,hK,hKs⟩ := SimplicialComplex.exists_finite_coordinate_closedBall
    (0 : V2) zero_le_one
  exact ⟨K,hK,hKs,K.affineOnFaces_affine toRectangle⟩

theorem fromRectangle_finitePL : FinitePiecewiseAffineOn fromRectangle Rect := by
  obtain ⟨H,hH,hvalue⟩ := toRectangle_finitePL.exists_homeomorph_image
    homeomorph.injective.injOn
  obtain ⟨p,hp,hpvalue⟩ := hH.symm
  have hp' : FinitePiecewiseAffineOn p Rect := toRectangle_image ▸ hp
  apply hp'.congr
  intro x hx
  let y : toRectangle '' Disk := ⟨x,toRectangle_image.symm.subset hx⟩
  have hq : toRectangle (H.symm y) = x :=
    (hvalue (H.symm y)).symm.trans (congrArg Subtype.val (H.apply_symm_apply y))
  have hv : (H.symm y : V2) = fromRectangle x :=
    homeomorph.injective (hq.trans (toRectangle_fromRectangle x).symm)
  exact (hpvalue y).symm.trans hv

theorem toRectangle_parameter (a b : ℝ) :
    toRectangle ![2*a-1,2*b-1] = (a,b) := toRectangle_fromRectangle (a,b)

theorem toRectangle_side_coordinates (z : V2) (v : ℝ) :
    ((toRectangle z).1 = v ↔ z 0 = 2*v-1) ∧
    ((toRectangle z).2 = v ↔ z 1 = 2*v-1) := by
  rw [toRectangle_apply]
  constructor <;> dsimp <;> constructor <;> intro h <;> linarith

theorem toRectangle_side_preimages :
    Disk ∩ toRectangle ⁻¹' ({(0 : ℝ)} ×ˢ I) = Disk ∩ {z | z 0 = -1} ∧
    Disk ∩ toRectangle ⁻¹' ({(1 : ℝ)} ×ˢ I) = Disk ∩ {z | z 0 = 1} ∧
    Disk ∩ toRectangle ⁻¹' (I ×ˢ {(0 : ℝ)}) = Disk ∩ {z | z 1 = -1} ∧
    Disk ∩ toRectangle ⁻¹' (I ×ˢ {(1 : ℝ)}) = Disk ∩ {z | z 1 = 1} := by
  have hfirst (v : ℝ) : Disk ∩ toRectangle ⁻¹' ({v} ×ˢ I) =
      Disk ∩ {z | z 0 = 2*v-1} := by
    ext z
    simp only [mem_inter_iff,mem_preimage,mem_prod,mem_singleton_iff,mem_ofPred_eq]
    constructor
    · rintro ⟨hz,he,_⟩
      exact ⟨hz,((toRectangle_side_coordinates z v).1).mp he⟩
    · rintro ⟨hz,he⟩
      exact ⟨hz,((toRectangle_side_coordinates z v).1).mpr he,
        (toRectangle_bijOn.1 hz).2⟩
  have hsecond (v : ℝ) : Disk ∩ toRectangle ⁻¹' (I ×ˢ {v}) =
      Disk ∩ {z | z 1 = 2*v-1} := by
    ext z
    simp only [mem_inter_iff,mem_preimage,mem_prod,mem_singleton_iff,mem_ofPred_eq]
    constructor
    · rintro ⟨hz,_,he⟩
      exact ⟨hz,((toRectangle_side_coordinates z v).2).mp he⟩
    · rintro ⟨hz,he⟩
      exact ⟨hz,(toRectangle_bijOn.1 hz).1,
        ((toRectangle_side_coordinates z v).2).mpr he⟩
  exact ⟨by convert hfirst 0 using 1; norm_num,by convert hfirst 1 using 1; norm_num,
    by convert hsecond 0 using 1; norm_num,by convert hsecond 1 using 1; norm_num⟩

theorem original_disk_of_rectangle
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {Q : Set X} {k : P2 → X}
    (hk : PolyhedralPLInCharts e k Rect)
    (hki : IsEmbedding (fun p : Rect => k p)) (hkQ : MapsTo k Rect Q)
    (hproper : ∀ p ∈ Rect, k p ∈ frontier Q ↔ p ∈ frontier Rect) :
    PolyhedralPLInCharts e (k ∘ toRectangle) Disk ∧
      IsEmbedding (fun z : Disk => k (toRectangle z)) ∧
      MapsTo (k ∘ toRectangle) Disk Q ∧
      (∀ z : Disk, k (toRectangle z) ∈ frontier Q ↔ (z : V2) ∈ Rim) ∧
      (k ∘ toRectangle) '' Disk = k '' Rect ∧
      (k ∘ toRectangle) '' Rim = k '' frontier Rect ∧
      (∀ t : ℝ, (k ∘ toRectangle) ![-1,2*t-1] = k (0,t)) ∧
      (∀ t : ℝ, (k ∘ toRectangle) ![1,2*t-1] = k (1,t)) ∧
      (∀ t : ℝ, (k ∘ toRectangle) ![2*t-1,-1] = k (t,0)) ∧
      (∀ t : ℝ, (k ∘ toRectangle) ![2*t-1,1] = k (t,1)) := by
  have hq := toRectangle_finitePL
  obtain ⟨K,hK,hKs,_⟩ := hq
  have hj : PolyhedralPLInCharts e (k ∘ toRectangle) Disk := by
    exact hKs ▸ hk.comp_finitePiecewiseAffineOn K hK (hKs.symm ▸ toRectangle_finitePL)
      (fun z hz => toRectangle_bijOn.1 (hKs.subset hz))
  let : CompactSpace Disk := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  refine ⟨hj,?_,fun z hz => hkQ (toRectangle_bijOn.1 hz),?_,?_,?_,?_,?_,?_,?_⟩
  · apply (hj.continuousOn.domRestrict.isClosedEmbedding ?_).isEmbedding
    intro x y hxy
    have h := hki.injective (a₁ := ⟨toRectangle x,toRectangle_bijOn.1 x.property⟩)
      (a₂ := ⟨toRectangle y,toRectangle_bijOn.1 y.property⟩) hxy
    exact Subtype.ext (homeomorph.injective (congrArg Subtype.val h))
  · intro z
    exact (hproper _ (toRectangle_bijOn.1 z.property)).trans (toRectangle_rim_iff z)
  · exact (image_image k toRectangle Disk).symm.trans (congrArg (fun s => k '' s) toRectangle_image)
  · exact (image_image k toRectangle Rim).symm.trans (congrArg (fun s => k '' s) toRectangle_rim_image)
  · intro t
    simp
  · intro t
    simp
  · intro t
    simp
  · intro t
    simp

end PoincareConjecture.M76.Dehn.Annuli.CubeCoordinates
