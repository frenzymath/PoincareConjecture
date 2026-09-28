import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.RimBands.Collar.Orientation.Collars.CollarNormalLabel
import PoincareConjecture.Proofs.M76.Rigidity.OriginalDiskProduct



set_option autoImplicit false

open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.RimBands

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "Disk" => closedBall (0 : V2) 1

theorem isPreconnected_disk_between {B : Set V2}
    (hB : ball (0 : V2) 1 ⊆ B) (hBD : B ⊆ Disk) : IsPreconnected B := by
  apply (convex_ball (0 : V2) 1).isPreconnected.subset_closure hB
  simpa only [closure_ball (0 : V2) (by norm_num : (1 : ℝ) ≠ 0)] using hBD

theorem exists_constant_disk_normal_label
    {X ι κ : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {Q S : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e Q j) {B : Set V2}
    (hB : ball (0 : V2) 1 ⊆ B) (hBD : B ⊆ Disk)
    (hbase : MapsTo j B S) (hSQ : S ∩ Q ⊆ j '' Disk)
    (E : κ → OpenPartialHomeomorph X C3)
    (hcover : ∀ x ∈ S, ∃ i, x ∈ (E i).source)
    (hpair : ∀ i y, y ∈ (E i).source → (y ∈ S ↔ (E i y).2 = 0))
    (hcompat : ∀ i k (x : S), (x : X) ∈ (E i).source ∩ (E k).source →
      ∃ V : Set X, IsOpen V ∧ (x : X) ∈ V ∧
        EqOn (fun y => SignType.sign (E i y).2) (fun y => SignType.sign (E k y).2) V) :
    ∃ s : SignType, s ≠ 0 ∧ ∀ z : B,
      PositiveCollarSignAt E (fun w : B × ℝ => P.map (w.1, w.2)) z s := by
  let F := fun w : B × ℝ => P.map (w.1, w.2)
  let U : Set (B × ℝ) := univ ×ˢ Ioo (-1 : ℝ) 1
  have hU : IsOpen U := isOpen_univ.prod isOpen_Ioo
  have hF : ContinuousOn F U := P.polyhedral.continuousOn.comp
    (continuous_subtype_val.comp continuous_fst |>.prodMk continuous_snd).continuousOn
    (fun z hz => ⟨hBD z.1.property, hz.2.1.le, hz.2.2.le⟩)
  have hzU (z : B) : (z, (0 : ℝ)) ∈ U := ⟨mem_univ _, by norm_num⟩
  have hzero : ∀ z ∈ U, F z ∈ S ↔ z.2 = 0 := by
    intro z hz
    have hzP : ((z.1 : V2), z.2) ∈ Disk ×ˢ Icc (-1 : ℝ) 1 :=
      ⟨hBD z.1.property, hz.2.1.le, hz.2.2.le⟩
    constructor
    · intro hS
      obtain ⟨w, hw, hwz⟩ := hSQ ⟨hS, P.inside hzP⟩
      have heq : (w, (0 : ℝ)) = ((z.1 : V2), z.2) :=
        P.injective ⟨hw, by norm_num⟩ hzP ((P.central w hw).trans hwz)
      exact (congrArg Prod.snd heq).symm
    · intro hz0
      change P.map (z.1, z.2) ∈ S
      rw [hz0, P.central z.1 (hBD z.1.property)]
      exact hbase z.1.property
  obtain ⟨ν, hν, hn, hgerm⟩ :=
    exists_collar_positive_normal_label hU F hF hzU hzero E hcover hpair hcompat
  let : PreconnectedSpace B := isPreconnected_iff_preconnectedSpace.mp
    (isPreconnected_disk_between hB hBD)
  let z₀ : B := ⟨0, hB (by simp)⟩
  exact ⟨ν z₀, hn z₀, fun z => (hν.apply_eq_of_preconnectedSpace z z₀) ▸ hgerm z⟩



theorem exists_constant_disk_normal_label_off_original_frontier
    {X ι κ : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {Q R S : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e Q j) (hQ : IsClosed Q) (hQR : Q ⊆ R)
    (himage : j '' Disk = S ∩ Q)
    (E : κ → OpenPartialHomeomorph X C3)
    (hcover : ∀ x ∈ S \ frontier R, ∃ i, x ∈ (E i).source)
    (hpair : ∀ i y, y ∈ (E i).source → (y ∈ S \ frontier R ↔ (E i y).2 = 0))
    (hcompat : ∀ i k (x : (S \ frontier R : Set X)), (x : X) ∈ (E i).source ∩ (E k).source →
      ∃ V : Set X, IsOpen V ∧ (x : X) ∈ V ∧
        EqOn (fun y => SignType.sign (E i y).2) (fun y => SignType.sign (E k y).2) V) :
    ∃ s : SignType, s ≠ 0 ∧
      ∀ z : (Disk ∩ j ⁻¹' (frontier R)ᶜ : Set V2),
        PositiveCollarSignAt E
          (fun w : (Disk ∩ j ⁻¹' (frontier R)ᶜ : Set V2) × ℝ => P.map (w.1, w.2)) z s := by
  let B := Disk ∩ j ⁻¹' (frontier R)ᶜ
  have hB : ball (0 : V2) 1 ⊆ B := by
    intro z hz
    have hzD : z ∈ Disk := ball_subset_closedBall hz
    have hcentral := P.central z hzD
    have hzQ : j z ∈ Q := hcentral ▸ P.inside ⟨hzD, by norm_num⟩
    have hzint : j z ∈ interior Q := by
      by_contra hn
      have hfront : j z ∈ frontier Q := ⟨hQ.closure_eq.symm ▸ hzQ, hn⟩
      have hRim := (P.proper (z, 0) ⟨hzD, by norm_num⟩).mp (hcentral.symm ▸ hfront)
      exact (ne_of_lt (mem_ball.mp hz)) (mem_sphere.mp hRim)
    exact ⟨hzD, fun hfront => hfront.2 (interior_mono hQR hzint)⟩
  apply exists_constant_disk_normal_label (S := S \ frontier R) (B := B)
    P hB inter_subset_left (E := E)
  · intro z hz
    exact ⟨(himage.subset (mem_image_of_mem j hz.1)).1, hz.2⟩
  · intro x hx
    exact himage.symm.subset ⟨hx.1.1, hx.2⟩
  · exact hcover
  · exact hpair
  · exact hcompat

end PoincareConjecture.M76.Dehn.Annuli.RimBands
