import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Coverings.OneSheet.OpenDomain









set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem ChartwisePLMap.mem_interior_image_of_locallyInjective
    {X Y ι κ : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {e : ι → OpenPartialHomeomorph X V3}
    {d : κ → OpenPartialHomeomorph Y V3} {R : Set X} {T : Set Y}
    {f : C(R, T)} (hf : ChartwisePLMap e d f)
    (hinj : IsLocallyInjective f) (x : R) (hx : (x : X) ∈ interior R) :
    (f x : Y) ∈ interior (range (fun y : R => (f y : Y))) := by
  classical
  obtain ⟨W, hW, hxW, hiW⟩ := hinj x
  obtain ⟨i, j, K, V, F, _, hV, hxV, _, hVi, hVK, _, _, hF, hvalue⟩ :=
    hf.coordinates x (mem_univ _)
  obtain ⟨A, hA, hAV⟩ := isOpen_induced_iff.mp (hV.inter hW)
  let O := interior R ∩ A
  have hO : IsOpen O := isOpen_interior.inter hA
  have hsource (y : X) (hy : y ∈ O) : y ∈ (e i).source := by
    have hyVW : (⟨y, interior_subset hy.1⟩ : R) ∈ V ∩ W := by
      rw [← hAV]
      exact hy.2
    exact hVi hyVW.1
  have hOsub : O ⊆ (e i).source := fun y hy => hsource y hy
  let U := (e i) '' O
  have hU : IsOpen U := (e i).isOpen_image_of_subset_source hO hOsub
  have hform (y : X) (hy : y ∈ O) :
      (f ⟨y, interior_subset hy.1⟩ : Y) ∈ (d j).source ∧
        F (e i y) = d j (f ⟨y, interior_subset hy.1⟩) := by
    have hyVW : (⟨y, interior_subset hy.1⟩ : R) ∈ V ∩ W := by
      rw [← hAV]
      exact hy.2
    exact hvalue ⟨y, interior_subset hy.1⟩ (hsource y hy)
      (hVK ⟨⟨y, interior_subset hy.1⟩, hyVW.1, rfl⟩)
  have hUK : U ⊆ K.space := by
    rintro z ⟨y, hy, rfl⟩
    have hyVW : (⟨y, interior_subset hy.1⟩ : R) ∈ V ∩ W := by
      rw [← hAV]
      exact hy.2
    exact hVK ⟨⟨y, interior_subset hy.1⟩, hyVW.1, rfl⟩
  have hFinj : InjOn F U := by
    rintro z ⟨y, hy, rfl⟩ w ⟨v, hv, rfl⟩ heq
    have hfy : (f ⟨y, interior_subset hy.1⟩ : Y) = f ⟨v, interior_subset hv.1⟩ :=
      (d j).injOn (hform y hy).1 (hform v hv).1
        ((hform y hy).2.symm.trans (heq.trans (hform v hv).2))
    have hyW : (⟨y, interior_subset hy.1⟩ : R) ∈ W := by
      have h : (⟨y, interior_subset hy.1⟩ : R) ∈ V ∩ W := by
        rw [← hAV]
        exact hy.2
      exact h.2
    have hvW : (⟨v, interior_subset hv.1⟩ : R) ∈ W := by
      have h : (⟨v, interior_subset hv.1⟩ : R) ∈ V ∩ W := by
        rw [← hAV]
        exact hv.2
      exact h.2
    exact congrArg (fun y : R => e i y) (hiW hyW hvW (Subtype.ext hfy))
  have hopenF : IsOpen (F '' U) :=
    (hF.locallyPiecewiseAffineOn_of_subset_interior hU
      (hU.subset_interior_iff.mpr hUK)).isOpen_image_of_injOn rfl hFinj
  have hFt : F '' U ⊆ (d j).target := by
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    rw [(hform y hy).2]
    exact (d j).map_source (hform y hy).1
  have hopen : IsOpen ((d j).symm '' (F '' U)) :=
    (d j).symm.isOpen_image_of_subset_source hopenF hFt
  have hsub : (d j).symm '' (F '' U) ⊆ range (fun y : R => (f y : Y)) := by
    rintro _ ⟨_, ⟨_, ⟨y, hy, rfl⟩, rfl⟩, rfl⟩
    rw [(hform y hy).2, (d j).left_inv (hform y hy).1]
    exact mem_range_self _
  have hxO : (x : X) ∈ O := ⟨hx, by
    have h : x ∈ V ∩ W := ⟨hxV, hxW⟩
    rw [← hAV] at h
    exact h⟩
  apply (interior_mono hsub)
  rw [hopen.interior_eq]
  refine ⟨F (e i x), ⟨e i x, ⟨x, hxO, rfl⟩, rfl⟩, ?_⟩
  rw [(hform x hxO).2, (d j).left_inv (hform x hxO).1]

theorem ChartwisePLMap.mapsTo_interior_of_locallyInjective
    {X Y ι κ : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {e : ι → OpenPartialHomeomorph X V3}
    {d : κ → OpenPartialHomeomorph Y V3} {R : Set X} {T : Set Y}
    {f : C(R, T)} (hf : ChartwisePLMap e d f)
    (hinj : IsLocallyInjective f) (x : R) (hx : (x : X) ∈ interior R) :
    (f x : Y) ∈ interior T :=
  interior_mono (by rintro _ ⟨y, rfl⟩; exact (f y).property)
    (hf.mem_interior_image_of_locallyInjective hinj x hx)

end PoincareConjecture.M76
