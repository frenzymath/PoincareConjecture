module

public import PoincareConjecture.Proofs.Horizon.Topology.Covering.Universal.BasedPath

public section
noncomputable section

open scoped unitInterval
open Topology

variable {X : Type*} [TopologicalSpace X]

namespace Poincare.Topology

@[ext]
structure UniversalCover (x₀ : X) where

  proj : X

  path : Path.Homotopic.Quotient x₀ proj

namespace UniversalCover

variable {x₀ x : X}

def ofBasedPath (x₀ : X) (α : BasedPath x₀) : UniversalCover x₀ :=
  mk (BasedPath.endpoint α) (Path.Homotopic.Quotient.mk α.toPath)

theorem ofBasedPath_def (α : BasedPath x₀) :
    ofBasedPath x₀ α =
      mk (BasedPath.endpoint α) (Path.Homotopic.Quotient.mk α.toPath) :=
  (rfl)

instance instTopologicalSpaceUniversalCover (x₀ : X) : TopologicalSpace (UniversalCover x₀) :=
  TopologicalSpace.coinduced (ofBasedPath x₀) inferInstance

@[fun_prop] theorem continuous_ofBasedPath (x₀ : X) : Continuous (ofBasedPath x₀) :=
  continuous_coinduced_rng

@[simp] theorem ofBasedPath_ofPath {y : X} (p : Path x₀ y) :
    ofBasedPath x₀ (BasedPath.ofPath p) = mk y (Path.Homotopic.Quotient.mk p) := by
  refine UniversalCover.ext p.target ?_
  apply Path.Homotopic.hpath_hext
  intro t
  rfl

theorem surjective_ofBasedPath (x₀ : X) : Function.Surjective (ofBasedPath x₀) := by
  intro z
  rcases z with ⟨x, q⟩
  induction q using Quotient.inductionOn with
  | h γ => exact ⟨BasedPath.ofPath γ, ofBasedPath_ofPath γ⟩

theorem isQuotientMap_ofBasedPath (x₀ : X) : IsQuotientMap (ofBasedPath x₀) :=
  ⟨⟨rfl⟩, surjective_ofBasedPath x₀⟩

@[simp]
theorem proj_ofBasedPath (x₀ : X) (γ : BasedPath x₀) :
    proj (ofBasedPath x₀ γ) = BasedPath.endpoint γ :=
  (rfl)

theorem endpoint_eq_of_ofBasedPath_eq {α β : BasedPath x₀}
    (h : ofBasedPath x₀ α = ofBasedPath x₀ β) :
    BasedPath.endpoint α = BasedPath.endpoint β := by
  simpa using congrArg (proj (x₀ := x₀)) h

theorem toPath_homotopic_of_ofBasedPath_eq {α β : BasedPath x₀}
    (h : ofBasedPath x₀ α = ofBasedPath x₀ β) :
    Path.Homotopic
      (α.toPath.cast rfl (endpoint_eq_of_ofBasedPath_eq h).symm)
      β.toPath := by
  rw [ofBasedPath] at h
  obtain ⟨hend, hq⟩ := UniversalCover.mk.injEq .. |>.mp h
  have hcast : HEq (Path.Homotopic.Quotient.mk α.toPath)
      (Path.Homotopic.Quotient.mk (α.toPath.cast rfl hend.symm)) :=
    Path.Homotopic.hpath_hext (fun _ ↦ rfl)
  exact Path.Homotopic.Quotient.exact (eq_of_heq (hcast.symm.trans hq))

theorem ofBasedPath_eq_of_homotopic_toPath {α β : BasedPath x₀}
    (heq : BasedPath.endpoint α = BasedPath.endpoint β)
    (h : Path.Homotopic (α.toPath.cast rfl heq.symm) β.toPath) :
    ofBasedPath x₀ α = ofBasedPath x₀ β := by
  rw [ofBasedPath]
  refine UniversalCover.ext heq ?_
  have h1 : HEq (Path.Homotopic.Quotient.mk α.toPath)
      (Path.Homotopic.Quotient.mk (α.toPath.cast rfl heq.symm)) :=
    Path.Homotopic.hpath_hext (fun _ ↦ rfl)
  exact h1.trans (heq_of_eq (Quotient.sound h))

@[fun_prop] theorem continuous_proj (x₀ : X) : Continuous (proj (x₀ := x₀)) := by
  rw [(isQuotientMap_ofBasedPath x₀).continuous_iff]
  exact BasedPath.continuous_endpoint

theorem isOpenMap_proj [LocallyPathConnectedSpace X] (x₀ : X) :
    IsOpenMap (proj (x₀ := x₀)) := by
  intro s hs
  have hs_pre : IsOpen (ofBasedPath x₀ ⁻¹' s) :=
    (isQuotientMap_ofBasedPath x₀).isOpen_preimage.2 hs
  have himage :
      proj (x₀ := x₀) '' s = BasedPath.endpoint '' (ofBasedPath x₀ ⁻¹' s) := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      rcases surjective_ofBasedPath x₀ z with ⟨γ, rfl⟩
      exact ⟨γ, hz, by simp [proj_ofBasedPath]⟩
    · rintro ⟨γ, hsγ, hγ⟩
      exact ⟨ofBasedPath x₀ γ, hsγ, by simpa [proj_ofBasedPath] using hγ⟩
  rw [himage]
  exact BasedPath.isOpenMap_endpoint x₀ _ hs_pre

def basedPathComponent (U : Set X) {y : X} (p : Path x₀ y) : Set (BasedPath x₀) :=
  pathComponentIn (BasedPath.endpoint (x₀ := x₀) ⁻¹' U) (BasedPath.ofPath p)

noncomputable def basedPathSheet (U : Set X) (hxU : x ∈ U)
    (q : Path.Homotopic.Quotient x₀ x) : Set (BasedPath x₀) :=
  Quotient.liftOn q (fun p : Path x₀ x ↦ basedPathComponent U p)
    fun _ _ h ↦ BasedPath.pathComponentIn_ofPath_eq_of_homotopic hxU h

@[simp] theorem basedPathSheet_mk (U : Set X) (hxU : x ∈ U) (p : Path x₀ x) :
    basedPathSheet U hxU (Path.Homotopic.Quotient.mk p) = basedPathComponent U p := (rfl)

theorem basedPathSheet_subset_endpoint_preimage (U : Set X) (hxU : x ∈ U)
    (q : Path.Homotopic.Quotient x₀ x) :
    basedPathSheet U hxU q ⊆ BasedPath.endpoint (x₀ := x₀) ⁻¹' U := by
  induction q using Quotient.inductionOn with
  | h p =>
    intro β hβ
    exact hβ.target_mem

noncomputable def sheet (U : Set X) (hxU : x ∈ U)
    (q : Path.Homotopic.Quotient x₀ x) : Set (UniversalCover x₀) :=
  ofBasedPath x₀ '' basedPathSheet U hxU q

theorem sheet_subset_proj_preimage (U : Set X) (hxU : x ∈ U) (q : Path.Homotopic.Quotient x₀ x) :
    sheet U hxU q ⊆ proj (x₀ := x₀) ⁻¹' U := by
  rintro _ ⟨α, hα, rfl⟩
  rw [Set.mem_preimage, proj_ofBasedPath]
  exact basedPathSheet_subset_endpoint_preimage U hxU q hα

private theorem pathComponent_preimage_eq_of_ofBasedPath_eq {U : Set X} {α β : BasedPath x₀}
    (hα_end : BasedPath.endpoint α ∈ U) (hαβ : ofBasedPath x₀ α = ofBasedPath x₀ β) :
    pathComponentIn (BasedPath.endpoint (x₀ := x₀) ⁻¹' U) α =
      pathComponentIn (BasedPath.endpoint (x₀ := x₀) ⁻¹' U) β := by
  have hβ_end : BasedPath.endpoint β ∈ U :=
    endpoint_eq_of_ofBasedPath_eq hαβ ▸ hα_end
  exact BasedPath.pathComponentIn_ofPath_eq_of_homotopic (x₀ := x₀) hβ_end
    (toPath_homotopic_of_ofBasedPath_eq hαβ)

private theorem mem_basedPathComponent_of_ofBasedPath_eq {U : Set X} {y : X} {p : Path x₀ y}
    {α β : BasedPath x₀} (hβ : β ∈ basedPathComponent U p)
    (hαβ : ofBasedPath x₀ α = ofBasedPath x₀ β) :
    α ∈ basedPathComponent U p := by
  have hα_end : BasedPath.endpoint α ∈ U :=
    (endpoint_eq_of_ofBasedPath_eq hαβ).symm ▸ hβ.target_mem
  unfold basedPathComponent
  have hself : α ∈ pathComponentIn (BasedPath.endpoint (x₀ := x₀) ⁻¹' U) α :=
    mem_pathComponentIn_self hα_end
  rw [pathComponent_preimage_eq_of_ofBasedPath_eq hα_end hαβ,
    pathComponentIn_congr hβ] at hself
  exact hself

theorem ofBasedPath_preimage_sheet (U : Set X) (hxU : x ∈ U) (q : Path.Homotopic.Quotient x₀ x) :
    ofBasedPath x₀ ⁻¹' sheet U hxU q = basedPathSheet U hxU q := by
  apply Set.Subset.antisymm
  · intro α hα
    obtain ⟨β, hβ, hαβ⟩ := hα
    induction q using Quotient.inductionOn with
    | h p =>

      exact mem_basedPathComponent_of_ofBasedPath_eq hβ hαβ.symm
  · intro α hα
    exact ⟨α, hα, rfl⟩

@[simp] theorem ofBasedPath_mem_sheet_iff {U : Set X} {hxU : x ∈ U}
    {q : Path.Homotopic.Quotient x₀ x} {α : BasedPath x₀} :
    ofBasedPath x₀ α ∈ sheet U hxU q ↔ α ∈ basedPathSheet U hxU q := by
  rw [← ofBasedPath_preimage_sheet U hxU q]; rfl

theorem isOpen_sheet [LocallyPathConnectedSpace X] [SemilocallySimplyConnectedSpace X]
    (U : Set X) (hU_open : IsOpen U) (hxU : x ∈ U) (q : Path.Homotopic.Quotient x₀ x) :
    IsOpen (sheet U hxU q) := by
  rw [(isQuotientMap_ofBasedPath x₀).isOpen_preimage.symm]
  rw [ofBasedPath_preimage_sheet]
  induction q using Quotient.inductionOn with
  | h p => exact BasedPath.isOpen_pathComponent_preimage hU_open _

theorem mem_sheet_self {U : Set X} (hxU : x ∈ U) (p : Path x₀ x) :
    ofBasedPath x₀ (BasedPath.ofPath p) ∈ sheet U hxU (Path.Homotopic.Quotient.mk p) :=
  ⟨BasedPath.ofPath p, mem_pathComponentIn_self
    (by simpa using hxU), rfl⟩

theorem proj_surjOn_sheet {U : Set X} (hU_pathConn : IsPathConnected U)
    (hxU : x ∈ U) (q : Path.Homotopic.Quotient x₀ x) :
    (sheet U hxU q).SurjOn (proj (x₀ := x₀)) U := by
  intro v hvU
  induction q using Quotient.inductionOn with
  | h p =>
    obtain ⟨δ, hδU⟩ := hU_pathConn.joinedIn x hxU v hvU
    let δ' : Path (BasedPath.endpoint (BasedPath.ofPath p)) v :=
      δ.cast (BasedPath.endpoint_ofPath p) rfl
    have hδ'_range : Set.range δ' ⊆ U := by
      rintro _ ⟨t, rfl⟩
      exact hδU t
    let γ := BasedPath.append (BasedPath.ofPath p) δ'
    have h_joined : JoinedIn (BasedPath.endpoint (x₀ := x₀) ⁻¹' U)
        (BasedPath.ofPath p) γ :=
      BasedPath.joinedIn_preimage_of_append (BasedPath.ofPath p) δ' hδ'_range
    have hγ_in : γ ∈ basedPathComponent U p := h_joined
    refine ⟨ofBasedPath x₀ γ, ⟨γ, hγ_in, rfl⟩, ?_⟩
    rw [proj_ofBasedPath]
    exact BasedPath.endpoint_append _ _

theorem pairwise_disjoint_sheet {U : Set X} (hU_slsc : IsPathHomotopyTrivial U) (hxU : x ∈ U) :
    Pairwise fun (q₁ q₂ : Path.Homotopic.Quotient x₀ x) ↦
      Disjoint (sheet U hxU q₁) (sheet U hxU q₂) := by
  intro q₁ q₂ hne
  refine Set.disjoint_iff.mpr ?_
  rintro e ⟨he₁, he₂⟩
  apply hne
  induction q₁ using Quotient.inductionOn with
  | h p₁ =>
    induction q₂ using Quotient.inductionOn with
    | h p₂ =>
      obtain ⟨α₁, hα₁, rfl⟩ := he₁
      obtain ⟨α₂, hα₂, hαeq⟩ := he₂
      have h_end_eq : BasedPath.endpoint (BasedPath.ofPath p₁) =
          BasedPath.endpoint (BasedPath.ofPath p₂) := by
        rw [BasedPath.endpoint_ofPath, BasedPath.endpoint_ofPath]
      have h_join : JoinedIn (BasedPath.endpoint (x₀ := x₀) ⁻¹' U)
          (BasedPath.ofPath p₁) (BasedPath.ofPath p₂) :=
        hα₁.trans (mem_basedPathComponent_of_ofBasedPath_eq hα₂ hαeq.symm).symm
      have h_uc_eq : ofBasedPath x₀ (BasedPath.ofPath p₁) =
          ofBasedPath x₀ (BasedPath.ofPath p₂) :=
        ofBasedPath_eq_of_homotopic_toPath h_end_eq
          (BasedPath.toPath_homotopic_of_joinedIn_pathHomotopyTrivial
            hU_slsc h_end_eq h_join)
      rw [ofBasedPath_ofPath, ofBasedPath_ofPath] at h_uc_eq
      exact eq_of_heq ((UniversalCover.mk.injEq _ _ _ _).mp h_uc_eq).2

theorem sheet_exhaustive {U : Set X} (hU_pathConn : IsPathConnected U) (hxU : x ∈ U) :
    (proj (x₀ := x₀) ⁻¹' U) ⊆ ⋃ q : Path.Homotopic.Quotient x₀ x, sheet U hxU q := by
  intro e he
  obtain ⟨α, rfl⟩ := surjective_ofBasedPath x₀ e
  rw [Set.mem_preimage, proj_ofBasedPath] at he

  obtain ⟨η, hη_range⟩ := hU_pathConn.joinedIn _ he x hxU

  let p : Path x₀ x := α.toPath.trans η

  rw [Set.mem_iUnion]
  refine ⟨Path.Homotopic.Quotient.mk p, ?_⟩
  simp only [sheet, basedPathSheet_mk, basedPathComponent]

  have h_join : JoinedIn (BasedPath.endpoint (x₀ := x₀) ⁻¹' U) α
      (BasedPath.append α η) :=
    BasedPath.joinedIn_preimage_of_append α η fun _ ⟨t, ht⟩ ↦ ht ▸ hη_range t
  exact ⟨α, h_join.symm, rfl⟩

theorem proj_injOn_sheet {U : Set X} (hU_slsc : IsPathHomotopyTrivial U)
    (hxU : x ∈ U) (q : Path.Homotopic.Quotient x₀ x) : (sheet U hxU q).InjOn (proj (x₀ := x₀)) := by
  rintro _ ⟨α₁, hα₁, rfl⟩ _ ⟨α₂, hα₂, rfl⟩ h_proj
  rw [proj_ofBasedPath, proj_ofBasedPath] at h_proj
  induction q using Quotient.inductionOn with
  | h p =>

    have h_joined : JoinedIn (BasedPath.endpoint (x₀ := x₀) ⁻¹' U) α₁ α₂ :=
      hα₁.symm.trans hα₂
    have h_homotopic : Path.Homotopic (α₁.toPath.cast rfl h_proj.symm) α₂.toPath :=
      BasedPath.toPath_homotopic_of_joinedIn_pathHomotopyTrivial hU_slsc h_proj h_joined
    exact ofBasedPath_eq_of_homotopic_toPath h_proj h_homotopic

end UniversalCover

end Poincare.Topology
