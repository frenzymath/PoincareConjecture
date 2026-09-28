import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.BoundaryGerm.MarkedMatching
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.BoundaryGerm.Extension
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.RadialBody

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.PlaneArcs.BoundaryGerm

private abbrev E1 := EuclideanSpace Real (Fin 1)
private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S1 := sphere (0 : E2) 1

private theorem exists_open_circle_patch
    (f : E1 → S1) {s r : Real} (hsr : s < r)
    (hfi : InjOn f (closedBall 0 r))
    (hfl : ∀ x ∈ closedBall (0 : E1) r,
      IsLocalDiffeomorphAt (𝓡 1) (𝓡 1) ∞ f x) :
    ∃ U : Set E2, IsOpen U ∧
      (fun x => (f x : E2)) '' closedBall (0 : E1) s ⊆ U ∧
      U ∩ sphere (0 : E2) 1 ⊆ (fun x => (f x : E2)) '' closedBall (0 : E1) r := by
  obtain ⟨e, hes, _, heq, _, _⟩ :=
    Poincare.exists_openPartialHomeomorph_of_injOn_compact
      (isCompact_closedBall 0 r) hfi hfl
  let V := e '' (e.source ∩ ball (0 : E1) r)
  have hVo : IsOpen V := e.isOpen_image_source_inter isOpen_ball
  obtain ⟨U, hU, hUV⟩ :=
    (Topology.IsInducing.isOpen_iff (f := (Subtype.val : S1 → E2))
      Topology.IsEmbedding.subtypeVal.isInducing).mp hVo
  refine ⟨U, hU, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    change f x ∈ Subtype.val ⁻¹' U
    rw [hUV]
    have hxr : x ∈ ball (0 : E1) r := closedBall_subset_ball hsr hx
    exact ⟨x, ⟨hes (ball_subset_closedBall hxr), hxr⟩,
      heq (hes (ball_subset_closedBall hxr))⟩
  · rintro x ⟨hxU, hxS⟩
    have hxV : (⟨x, hxS⟩ : S1) ∈ V := by rw [← hUV]; exact hxU
    obtain ⟨y, ⟨hye, hyr⟩, hey⟩ := hxV
    exact ⟨y, ball_subset_closedBall hyr,
      congrArg Subtype.val ((heq hye).symm.trans hey)⟩

theorem exists_disk_matching_fixing_common_arc_neighborhood
    (A B : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    {r : Real} (hr : 1 < r)
    (f g : E1 → S1)
    (hfi : InjOn f (closedBall 0 r))
    (hfl : ∀ x ∈ closedBall (0 : E1) r,
      IsLocalDiffeomorphAt (𝓡 1) (𝓡 1) ∞ f x)
    (hgi : InjOn g (closedBall 0 r))
    (hgl : ∀ x ∈ closedBall (0 : E1) r,
      IsLocalDiffeomorphAt (𝓡 1) (𝓡 1) ∞ g x)
    (hmark : ∀ x ∈ closedBall (0 : E1) r, A (f x) = B (g x))
    (V : Set E2) (hV : IsOpen V)
    (hmarkV : (fun x => A (f x)) '' closedBall (0 : E1) r ⊆ V)
    (hside : V ∩ (A '' closedBall 0 1) = V ∩ (B '' closedBall 0 1)) :
    ∃ E : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
      E '' (A '' closedBall 0 1) = B '' closedBall 0 1 ∧
      ∃ W : Set E2, IsOpen W ∧
        (fun x => A (f x)) '' closedBall (0 : E1) 1 ⊆ W ∧
        ∀ x ∈ W, E x = x := by
  have hrpos : 0 < r := zero_lt_one.trans hr
  obtain ⟨Q, hQball, hQmark⟩ := exists_marked_disk_matching A B hrpos f g hfi hfl hgi hgl
  have hQfix (x : E1) (hx : x ∈ closedBall 0 r) : Q (A (f x)) = A (f x) :=
    (hQmark x hx).trans (hmark x hx).symm
  let D := A.trans (Q.trans A.symm)
  have hDapply (x : E2) : D x = A.symm (Q (A x)) := rfl
  have hDfix (x : E1) (hx : x ∈ closedBall 0 r) : D (f x) = (f x : E2) := by
    rw [hDapply, hQfix x hx, A.symm_apply_apply]
  obtain ⟨ρ, hρ, hρr⟩ := exists_between hr
  let P : Set E2 := (fun x => (f x : E2)) '' closedBall (0 : E1) ρ
  let K : Set E2 := (fun x => (f x : E2)) '' closedBall (0 : E1) 1
  have hfr : ContinuousOn (fun x => (f x : E2)) (closedBall (0 : E1) r) :=
    continuous_subtype_val.comp_continuousOn
      (fun x hx => (hfl x hx).contMDiffAt.continuousAt.continuousWithinAt)
  have hP : IsCompact P := (isCompact_closedBall _ _).image_of_continuousOn
    (hfr.mono (closedBall_subset_closedBall hρr.le))
  have hK : IsCompact K := (isCompact_closedBall _ _).image_of_continuousOn
    (hfr.mono (closedBall_subset_closedBall hr.le))
  have hKP : K ⊆ P := image_mono (closedBall_subset_closedBall hρ.le)
  obtain ⟨T, hT, hPT, hTr⟩ := exists_open_circle_patch f hρr hfi hfl
  obtain ⟨U, hU, hKU, hUP⟩ := exists_open_circle_patch f hρ
    (hfi.mono (closedBall_subset_closedBall hρr.le))
    (fun x hx => hfl x (closedBall_subset_closedBall hρr.le hx))
  have hPV : P ⊆ T ∩ sphere (0 : E2) 1 := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨hPT (mem_image_of_mem _ hx), (f x).property⟩
  have hfix : ∀ x ∈ T ∩ sphere (0 : E2) 1, D x = x := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hTr hx
    exact hDfix y hy
  have hinj (x : E2) (_ : x ∈ P) : Injective (fderiv Real D x) := by
    have h := (D.mfderivToContinuousLinearEquiv (by simp) x).injective
    change Injective (mfderiv (𝓡 2) (𝓡 2) D x) at h
    simpa only [mfderiv_eq_fderiv, TangentSpace] using h
  have hinside : ∀ x ∈ P, ∀ᶠ s in 𝓝[<] (0 : Real), ‖D ((1 + s) • x)‖ ≤ 1 := by
    rintro _ ⟨y, hy, rfl⟩
    have hyr : y ∈ closedBall (0 : E1) r := closedBall_subset_closedBall hρr.le hy
    have hc : Continuous (fun s : Real => Q (A ((1 + s) • (f y : E2)))) :=
      Q.continuous.comp (A.continuous.comp
        ((continuous_const.add continuous_id).smul continuous_const))
    have hev : ∀ᶠ s in 𝓝 (0 : Real), Q (A ((1 + s) • (f y : E2))) ∈ V := by
      apply hc.continuousAt.eventually
      change V ∈ 𝓝 (Q (A ((1 + (0 : Real)) • (f y : E2))))
      rw [add_zero, one_smul, hQfix y hyr]
      exact hV.mem_nhds (hmarkV (mem_image_of_mem _ hyr))
    filter_upwards [hev.filter_mono nhdsWithin_le_nhds,
      Ioo_mem_nhdsLT (show (-1 : Real) < 0 by norm_num)] with s hsV hs
    have hrad : (1 + s) • (f y : E2) ∈ closedBall (0 : E2) 1 := by
      rw [mem_closedBall_zero_iff, norm_smul, norm_eq_of_mem_sphere (f y), mul_one,
        Real.norm_eq_abs, abs_of_pos (by linarith [hs.1] : 0 < 1 + s)]
      linarith [hs.2]
    have htarget : Q (A ((1 + s) • (f y : E2))) ∈ B '' closedBall 0 1 :=
      hQball ▸ mem_image_of_mem Q (mem_image_of_mem A hrad)
    have hsource : Q (A ((1 + s) • (f y : E2))) ∈ A '' closedBall 0 1 :=
      (hside.symm ▸ (show Q (A ((1 + s) • (f y : E2))) ∈
        V ∩ (B '' closedBall 0 1) from ⟨hsV, htarget⟩)).2
    obtain ⟨z, hz, hez⟩ := hsource
    rw [hDapply, ← hez, A.symm_apply_apply]
    exact mem_closedBall_zero_iff.mp hz
  obtain ⟨S, _, _, W, hW, hKW, F, _, hFD, hFsphere⟩ :=
    exists_supported_extension_of_inward_circle_patch D.contDiff hP hK hKP
      hT hPV hfix hinj hinside hU hKU hUP
  have hFboundary : F.toHomeomorph '' sphere (0 : E2) 1 =
      (Homeomorph.refl E2) '' sphere (0 : E2) 1 := by
    change F '' sphere (0 : E2) 1 = id '' sphere (0 : E2) 1
    exact image_congr hFsphere
  have hdim : 1 < Module.rank Real E2 := by rw [← Module.finrank_eq_rank]; norm_num
  have hFball : F '' closedBall (0 : E2) 1 = closedBall 0 1 := by
    simpa using F.toHomeomorph.image_closedBall_eq_of_image_sphere_eq
      (Homeomorph.refl E2) hdim hFboundary
  have hFsymm : F.symm '' closedBall 0 1 = closedBall 0 1 := by
    calc
      F.symm '' closedBall 0 1 = F.symm '' (F '' closedBall 0 1) :=
        congrArg (image F.symm) hFball.symm
      _ = closedBall 0 1 := F.toEquiv.symm_image_image _
  let E := A.symm.trans (F.symm.trans (A.trans Q))
  have hAsymm : A.symm '' (A '' closedBall 0 1) = closedBall 0 1 :=
    A.toEquiv.symm_image_image _
  refine ⟨E, ?_, A '' (F '' W), A.toHomeomorph.isOpenMap _
    (F.toHomeomorph.isOpenMap _ hW), ?_, ?_⟩
  · change (Q ∘ A ∘ F.symm ∘ A.symm) '' (A '' closedBall 0 1) = _
    rw [image_comp, image_comp, image_comp, hAsymm, hFsymm, hQball]
  · rintro _ ⟨x, hx, rfl⟩
    refine mem_image_of_mem A ⟨f x, hKW (mem_image_of_mem _ hx), ?_⟩
    exact (hFD (hKW (mem_image_of_mem _ hx))).trans
      (hDfix x (closedBall_subset_closedBall hr.le hx))
  · rintro _ ⟨z, ⟨y, hy, rfl⟩, rfl⟩
    change Q (A (F.symm (A.symm (A (F y))))) = A (F y)
    rw [A.symm_apply_apply, F.symm_apply_apply, hFD hy, hDapply, A.apply_symm_apply]

end Poincare.Manifold.Schoenflies.PlaneArcs.BoundaryGerm
