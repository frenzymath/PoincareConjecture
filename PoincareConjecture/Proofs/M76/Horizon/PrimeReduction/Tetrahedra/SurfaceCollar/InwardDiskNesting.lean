import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.SurfaceCollar.InwardAnnulus










set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76

theorem inward_motion_disk_subset_sdiff
    {X : Type*} [TopologicalSpace X]
    {D E S R r O : Set X} (hD : IsClosed D) (hE : IsClosed E)
    (hconn : IsPreconnected D) (hwhole : D ∪ E = S) (hinter : D ∩ E = r)
    (hrfront : r ⊆ frontier R) (hDO : D ∩ O ⊆ R)
    {p : X} (hp : p ∈ D \ r) (hpO : p ∉ O)
    (H : X ≃ₜ X) (hfix : EqOn H id Oᶜ)
    (hS : ∀ x, H x ∈ S ↔ x ∈ S)
    (hin : ∀ x ∈ R, H x ∈ interior R ∨ H x = x)
    (hrin : H '' r ⊆ interior R) : H '' D ⊆ D \ r := by
  have havoid : Disjoint (H '' D) r := by
    apply disjoint_left.mpr
    rintro z ⟨x,hx,rfl⟩ hzr
    have hznot : H x ∉ interior R := (hrfront hzr).2
    by_cases hxO : x ∈ O
    · rcases hin x (hDO ⟨hx,hxO⟩) with hi | hf
      · exact hznot hi
      · exact hznot (hrin ⟨x,hf ▸ hzr,rfl⟩)
    · have hf : H x = x := hfix hxO
      exact hznot (hrin ⟨x,hf ▸ hzr,rfl⟩)
  have hHD : IsPreconnected (H '' D) := hconn.image _ H.continuous.continuousOn
  have hcov : H '' D ⊆ D ∪ E := by
    rintro _ ⟨x,hx,rfl⟩
    exact hwhole.symm.subset ((hS x).mpr (hwhole.subset (Or.inl hx)))
  have hpfix : H p = p := hfix hpO
  have hpHD : p ∈ H '' D := ⟨p,hp.1,hpfix⟩
  have hpE : p ∉ E := fun h => hp.2 (hinter.subset ⟨hp.1,h⟩)
  intro z hz
  refine ⟨?_,fun hr => disjoint_left.mp havoid hz hr⟩
  by_contra hzD
  have hcover : H '' D ⊆ Eᶜ ∪ Dᶜ := by
    intro x hx
    by_cases hxE : x ∈ E
    · exact Or.inr (fun hxD => disjoint_left.mp havoid hx (hinter.subset ⟨hxD,hxE⟩))
    · exact Or.inl hxE
  obtain ⟨x,hx,hxE,hxD⟩ := hHD Eᶜ Dᶜ hE.isOpen_compl hD.isOpen_compl hcover
    ⟨p,hpHD,hpE⟩ ⟨z,hz,hzD⟩
  exact (hcov hx).elim hxD hxE

theorem exists_inward_disk_nesting_support
    {X : Type*} [TopologicalSpace X] [T2Space X]
    {f : (ℝ × ℝ) → X} (hf : ContinuousOn f (closedBall (0 : ℝ × ℝ) 1))
    (hfi : InjOn f (closedBall (0 : ℝ × ℝ) 1))
    {E S R V : Set X} (hE : IsClosed E)
    (hwhole : (f '' closedBall (0 : ℝ × ℝ) 1) ∪ E = S)
    (hinter : (f '' closedBall (0 : ℝ × ℝ) 1) ∩ E = f '' sphere (0 : ℝ × ℝ) 1)
    (hrfront : f '' sphere (0 : ℝ × ℝ) 1 ⊆ frontier R)
    {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hshell : f '' {x : ℝ × ℝ | ‖x‖ ∈ Icc a 1} ⊆ R)
    (hV : IsOpen V) (hrV : f '' sphere (0 : ℝ × ℝ) 1 ⊆ V) :
    ∃ O : Set X, IsOpen O ∧ f '' sphere (0 : ℝ × ℝ) 1 ⊆ O ∧ O ⊆ V ∧
      Disjoint O (f '' closedBall (0 : ℝ × ℝ) a) ∧
      ∀ H : X ≃ₜ X, EqOn H id Oᶜ → (∀ x, H x ∈ S ↔ x ∈ S) →
        (∀ x ∈ R, H x ∈ interior R ∨ H x = x) →
        H '' (f '' sphere (0 : ℝ × ℝ) 1) ⊆ interior R →
        H '' (f '' closedBall (0 : ℝ × ℝ) 1) ⊆
          (f '' closedBall (0 : ℝ × ℝ) 1) \ (f '' sphere (0 : ℝ × ℝ) 1) := by
  let core := f '' closedBall (0 : ℝ × ℝ) a
  have haD : closedBall (0 : ℝ × ℝ) a ⊆ closedBall (0 : ℝ × ℝ) 1 :=
    closedBall_subset_closedBall ha1.le
  have hcore : IsClosed core :=
    ((isCompact_closedBall (0 : ℝ × ℝ) a).image_of_continuousOn (hf.mono haD)).isClosed
  let O := V ∩ coreᶜ
  have hO : IsOpen O := hV.inter hcore.isOpen_compl
  have hrO : f '' sphere (0 : ℝ × ℝ) 1 ⊆ O := by
    rintro _ ⟨x,hx,rfl⟩
    refine ⟨hrV ⟨x,hx,rfl⟩,?_⟩
    rintro ⟨y,hy,hyx⟩
    have hyx' := hfi (haD hy) (sphere_subset_closedBall hx) hyx
    have hb := mem_closedBall_zero_iff.mp hy
    rw [hyx',mem_sphere_zero_iff_norm.mp hx] at hb
    exact (not_le_of_gt ha1) hb
  refine ⟨O,hO,hrO,inter_subset_left,disjoint_left.mpr (fun _ hO hc => hO.2 hc),?_⟩
  intro H hfix hS hin hrin
  have hD : IsClosed (f '' closedBall (0 : ℝ × ℝ) 1) :=
    ((isCompact_closedBall (0 : ℝ × ℝ) 1).image_of_continuousOn hf).isClosed
  have hconn : IsPreconnected (f '' closedBall (0 : ℝ × ℝ) 1) :=
    (convex_closedBall (0 : ℝ × ℝ) 1).isPreconnected.image _ hf
  have hDO : (f '' closedBall (0 : ℝ × ℝ) 1) ∩ O ⊆ R := by
    rintro _ ⟨⟨x,hx,rfl⟩,hxO⟩
    apply hshell
    refine ⟨x,⟨?_,mem_closedBall_zero_iff.mp hx⟩,rfl⟩
    by_contra! hlt
    exact hxO.2 ⟨x,mem_closedBall_zero_iff.mpr hlt.le,rfl⟩
  have hzero : (0 : ℝ × ℝ) ∈ closedBall (0 : ℝ × ℝ) 1 := by simp
  have hp : f 0 ∈ (f '' closedBall (0 : ℝ × ℝ) 1) \ (f '' sphere (0 : ℝ × ℝ) 1) := by
    refine ⟨mem_image_of_mem f hzero,?_⟩
    rintro ⟨x,hx,hx0⟩
    have hx0' := hfi (sphere_subset_closedBall hx) hzero hx0
    simp [hx0'] at hx
  have hpO : f 0 ∉ O := fun h => h.2 ⟨0,mem_closedBall_self ha.le,rfl⟩
  exact inward_motion_disk_subset_sdiff hD hE hconn hwhole hinter hrfront hDO
    hp hpO H hfix hS hin hrin

theorem moved_disk_annulus_subset_shell
    {X : Type*} [TopologicalSpace X]
    {f : (ℝ × ℝ) → X} {a : ℝ} (ha1 : a < 1)
    {O : Set X} (hcore : Disjoint O (f '' closedBall (0 : ℝ × ℝ) a))
    (H : X ≃ₜ X) (hfix : EqOn H id Oᶜ) :
    (f '' closedBall (0 : ℝ × ℝ) 1) \
        (H '' (f '' (closedBall (0 : ℝ × ℝ) 1 \
          sphere (0 : ℝ × ℝ) 1))) ⊆
      f '' {x : ℝ × ℝ | ‖x‖ ∈ Icc a 1} := by
  rintro y ⟨⟨x,hx,rfl⟩,hnot⟩
  refine ⟨x,⟨?_,mem_closedBall_zero_iff.mp hx⟩,rfl⟩
  by_contra! hlt
  have hxcore : f x ∈ f '' closedBall (0 : ℝ × ℝ) a :=
    ⟨x,mem_closedBall_zero_iff.mpr hlt.le,rfl⟩
  have hxO : f x ∉ O := fun h => disjoint_left.mp hcore h hxcore
  apply hnot
  refine ⟨f x,⟨x,⟨hx,?_⟩,rfl⟩,hfix hxO⟩
  intro hr
  exact (hlt.trans ha1).ne (mem_sphere_zero_iff_norm.mp hr)

end PoincareConjecture.M76
