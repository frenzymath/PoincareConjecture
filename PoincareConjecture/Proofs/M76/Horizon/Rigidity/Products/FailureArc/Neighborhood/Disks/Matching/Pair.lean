import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.Matching.Rescaling
import PoincareConjecture.Proofs.M76.Rigidity.OriginalMarkedProductConstruction



set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1

theorem exists_disjoint_original_marked_disk_products
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X}
    (hR : IsCompact R) (he : PLDomain e R)
    (j : Bool → V2 → X)
    (hj : ∀ b, PolyhedralPLInCharts e (j b) Disk)
    (hi : ∀ b, IsEmbedding (fun z : Disk => j b z))
    (hjR : ∀ b, MapsTo (j b) Disk R)
    (hp : ∀ b, ∀ z : Disk, j b z ∈ frontier R ↔ (z : V2) ∈ Rim)
    (hdis : Disjoint (j false '' Disk) (j true '' Disk))
    (F : Bool → V2 × ℝ → X)
    (hF : ∀ b, PolyhedralPLInCharts e (F b) (Rim ×ˢ I))
    (hFi : ∀ b, InjOn (F b) (Rim ×ˢ I))
    (hfront : ∀ b, MapsTo (F b) (Rim ×ˢ I) (frontier R))
    (hcenter : ∀ b, ∀ z ∈ Rim, F b (z,0) = j b z)
    (hopenF : ∀ b, IsOpen ((Subtype.val : frontier R → X) ⁻¹'
      (F b '' (Rim ×ˢ Ioo (-1 : ℝ) 1))))
    (radius : Bool → ℝ) (hradius : ∀ b, 0 < radius b) :
    ∃ w : ℝ, 0 < w ∧ ∃ P : (b : Bool) → OriginalDiskProduct e R (j b),
      (∀ b, w / radius b ≤ 1/2) ∧
      Disjoint ((P false).map '' (Disk ×ˢ I)) ((P true).map '' (Disk ×ˢ I)) ∧
      (∀ b, ∀ z ∈ Rim, ∀ t ∈ I, (P b).map (z,t) = F b (z,(w / radius b)*t)) ∧
      ∀ b, ∀ v : ℝ, 0 < v → v ≤ 1 →
        IsOpen ((Subtype.val : R → X) ⁻¹' ((P b).map '' (Disk ×ˢ Ioo (-v) v))) ∧
        IsOpen ((Subtype.val : frontier R → X) ⁻¹' ((P b).map '' (Rim ×ˢ Ioo (-v) v))) := by
  have hj1compact : IsCompact (j true '' Disk) :=
    (isCompact_closedBall _ _).image_of_continuousOn (hj true).continuousOn
  obtain ⟨a₀,ha₀,ha₀small,P₀,hP₀,hmark₀,hopen₀⟩ :=
    exists_small_original_marked_disk_product hR he (hj false) (hi false)
      (hjR false) (hp false) (F false) (hF false) (hFi false) (hfront false)
      (hcenter false) (hopenF false) hj1compact.isClosed.isOpen_compl
      (fun _ hx hy => disjoint_left.mp hdis hx hy)
  have hP₀compact : IsCompact (P₀.map '' (Disk ×ˢ I)) :=
    ((isCompact_closedBall _ _).prod isCompact_Icc).image_of_continuousOn P₀.polyhedral.continuousOn
  have hj1avoid : j true '' Disk ⊆ (P₀.map '' (Disk ×ˢ I))ᶜ := by
    rintro _ hx ⟨z,hz,rfl⟩
    exact hP₀ hz hx
  obtain ⟨a₁,ha₁,ha₁small,P₁,hP₁,hmark₁,hopen₁⟩ :=
    exists_small_original_marked_disk_product hR he (hj true) (hi true)
      (hjR true) (hp true) (F true) (hF true) (hFi true) (hfront true)
      (hcenter true) (hopenF true) hP₀compact.isClosed.isOpen_compl hj1avoid
  let a : Bool → ℝ := fun b => if b then a₁ else a₀
  let P : (b : Bool) → OriginalDiskProduct e R (j b) := Bool.rec P₀ P₁
  have ha : ∀ b, 0 < a b := by intro b; cases b <;> assumption
  have hasmall : ∀ b, a b ≤ 1/2 := by intro b; cases b <;> assumption
  have hmark : ∀ b, ∀ z ∈ Rim, ∀ t ∈ I, (P b).map (z,t) = F b (z,a b*t) := by
    intro b; cases b <;> assumption
  have hopen : ∀ b, ∀ v : ℝ, 0 < v → v ≤ 1 →
      IsOpen ((Subtype.val : R → X) ⁻¹' ((P b).map '' (Disk ×ˢ Ioo (-v) v))) ∧
      IsOpen ((Subtype.val : frontier R → X) ⁻¹' ((P b).map '' (Rim ×ˢ Ioo (-v) v))) := by
    intro b; cases b <;> assumption
  have hrawdis : Disjoint ((P false).map '' (Disk ×ˢ I)) ((P true).map '' (Disk ×ˢ I)) := by
    apply disjoint_left.mpr
    rintro _ hx ⟨z,hz,rfl⟩
    exact hP₁ hz hx
  let w := min (radius false*a₀) (radius true*a₁) / 2
  have hmin : 0 < min (radius false*a₀) (radius true*a₁) :=
    lt_min (mul_pos (hradius false) ha₀) (mul_pos (hradius true) ha₁)
  have hw : 0 < w := div_pos hmin (by norm_num)
  have hwa (b : Bool) : w ≤ radius b*a b := by
    have hwmin : w ≤ min (radius false*a₀) (radius true*a₁) := by dsimp [w]; linarith
    cases b
    · exact hwmin.trans (min_le_left _ _)
    · exact hwmin.trans (min_le_right _ _)
  have hquot (b : Bool) : w / radius b ≤ a b :=
    (div_le_iff₀ (hradius b)).mpr (by simpa only [mul_comm] using hwa b)
  have hex (b : Bool) := exists_narrower_original_marked_disk_product
    (P b) (F b) (ha b) (div_pos hw (hradius b)) (hquot b)
    (U := univ) (fun _ _ => mem_univ _) (hmark b) (hopen b)
  choose Q hQ hQU hQsub hQmark hQopen using hex
  refine ⟨w,hw,Q,fun b => (hquot b).trans (hasmall b),
    hrawdis.mono (hQsub false) (hQsub true),hQmark,hQopen⟩

end PoincareConjecture.M76.Dehn.Annuli
