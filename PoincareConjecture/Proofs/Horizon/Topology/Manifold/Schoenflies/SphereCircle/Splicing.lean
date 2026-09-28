import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Immersion.FiniteDimensional
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Collar.Differential

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1
private instance : Fact (Module.finrank Real E3 = 2 + 1) := ⟨by simp⟩

theorem exists_smooth_sphere_disk_splicing
    {f : S2 -> E3} (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    (e : OpenPartialHomeomorph E2 S2)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    {r R : Real} (_hr : 0 < r) (hrR : r < R)
    (hsource : closedBall 0 R ⊆ e.source)
    (g : E2 -> E3) (hg : ContDiff Real ∞ g)
    (hginj : InjOn g (closedBall 0 r))
    (hgder : ∀ x ∈ closedBall 0 r, Injective (fderiv Real g x))
    (hagrees : ∀ x, r ≤ ‖x‖ -> ‖x‖ ≤ R -> g x = f (e x))
    (hdisjoint : Disjoint (g '' ball 0 r) (f '' (e '' ball 0 r)ᶜ)) :
    ∃ f' : S2 -> E3,
      _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f' ∧
      (∀ x ∈ closedBall 0 r, f' (e x) = g x) ∧
      (∀ y ∉ e '' ball 0 r, f' y = f y) ∧
      range f' = g '' closedBall 0 r ∪ f '' (e '' ball 0 r)ᶜ := by
  classical
  let U := e '' ball (0 : E2) r
  let V := e '' ball (0 : E2) R
  let K := e '' closedBall (0 : E2) r
  have hsr : closedBall (0 : E2) r ⊆ e.source :=
    (closedBall_subset_closedBall hrR.le).trans hsource
  have hV : IsOpen V :=
    e.isOpen_image_of_subset_source isOpen_ball (ball_subset_closedBall.trans hsource)
  have hK : IsClosed K :=
    ((isCompact_closedBall 0 r).image_of_continuousOn (e.continuousOn.mono hsr)).isClosed
  have hUK : U ⊆ K := image_mono ball_subset_closedBall
  have hKV : K ⊆ V := image_mono (closedBall_subset_ball hrR)
  have hVT : V ⊆ e.target := by
    rintro y ⟨x, hx, rfl⟩
    exact e.map_source (hsource (ball_subset_closedBall hx))
  have hcoords (y : S2) (hy : y ∈ V) : e.symm y ∈ ball (0 : E2) R := by
    obtain ⟨x, hx, rfl⟩ := hy
    rwa [e.left_inv (hsource (ball_subset_closedBall hx))]
  let f' : S2 -> E3 := V.piecewise (g ∘ e.symm) f
  have hinside (y : S2) (hy : y ∈ V) : f' y = g (e.symm y) :=
    piecewise_eq_of_mem V _ _ hy
  have hoff (y : S2) (hy : y ∉ U) : f' y = f y := by
    by_cases hyV : y ∈ V
    · rw [hinside y hyV]
      have hlo : r ≤ ‖e.symm y‖ := by
        by_contra hn
        exact hy ⟨e.symm y, mem_ball_zero_iff.mpr (lt_of_not_ge hn), e.right_inv (hVT hyV)⟩
      rw [hagrees _ hlo (mem_ball_zero_iff.mp (hcoords y hyV)).le, e.right_inv (hVT hyV)]
    · exact piecewise_eq_of_notMem V _ _ hyV
  have hpatch (x : E2) (hx : x ∈ closedBall 0 r) : f' (e x) = g x := by
    rw [hinside (e x) ⟨x, closedBall_subset_ball hrR hx, rfl⟩, e.left_inv (hsr hx)]
  have hlocalG (y : S2) (hy : y ∈ V) : f' =ᶠ[𝓝 y] g ∘ e.symm := by
    filter_upwards [hV.mem_nhds hy] with z hz
    exact hinside z hz
  have hlocalF (y : S2) (hy : y ∉ K) : f' =ᶠ[𝓝 y] f := by
    filter_upwards [hK.isOpen_compl.mem_nhds hy] with z hz
    exact hoff z (fun hzU => hz (hUK hzU))
  have hgs (y : S2) (hy : y ∈ V) : ContMDiffAt (𝓡 2) (𝓡 3) ∞ (g ∘ e.symm) y :=
    hg.contMDiff.contMDiffAt.comp y
      (hei.contMDiffAt (e.open_target.mem_nhds (hVT hy)))
  have hf's : ContMDiff (𝓡 2) (𝓡 3) ∞ f' := by
    intro y
    by_cases hy : y ∈ K
    · exact (hgs y (hKV hy)).congr_of_eventuallyEq (hlocalG y (hKV hy))
    · exact (hf.contMDiff y).congr_of_eventuallyEq (hlocalF y hy)
  have hf'inj : Injective f' := by
    intro y z hyz
    by_cases hy : y ∈ U
    · obtain ⟨x, hx, rfl⟩ := hy
      by_cases hz : z ∈ U
      · obtain ⟨w, hw, rfl⟩ := hz
        rw [hpatch _ (ball_subset_closedBall hx), hpatch _ (ball_subset_closedBall hw)] at hyz
        exact congrArg e (hginj (ball_subset_closedBall hx) (ball_subset_closedBall hw) hyz)
      · rw [hpatch _ (ball_subset_closedBall hx), hoff z hz] at hyz
        exact (disjoint_left.mp hdisjoint (mem_image_of_mem g hx) ⟨z, hz, hyz.symm⟩).elim
    · by_cases hz : z ∈ U
      · obtain ⟨w, hw, rfl⟩ := hz
        rw [hoff y hy, hpatch _ (ball_subset_closedBall hw)] at hyz
        exact (disjoint_left.mp hdisjoint (mem_image_of_mem g hw) ⟨y, hy, hyz⟩).elim
      · rw [hoff y hy, hoff z hz] at hyz
        exact hf.isEmbedding.injective hyz
  have hf'der (y : S2) : Injective (mfderiv (𝓡 2) (𝓡 3) f' y) := by
    by_cases hy : y ∈ K
    · have hyV := hKV hy
      have hxy : e.symm y ∈ closedBall (0 : E2) r := by
        obtain ⟨x, hx, rfl⟩ := hy
        rwa [e.left_inv (hsr hx)]
      have hem : e.MDifferentiable (𝓡 2) (𝓡 2) :=
        ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
      rw [(hlocalG y hyV).mfderiv_eq, mfderiv_comp y
        (hg.contMDiff.mdifferentiable (by simp) (e.symm y))
        (hem.mdifferentiableAt_symm (hVT hyV)), mfderiv_eq_fderiv]
      exact (hgder _ hxy).comp (hem.symm.mfderiv_injective (hVT hyV))
    · rw [(hlocalF y hy).mfderiv_eq]
      exact injective_mfderiv_sphere_embedding hf y
  refine ⟨f', Poincare.Geometry.Manifold.isSmoothEmbedding_of_injective_mfderiv
    hf's hf'inj hf'der, hpatch, hoff, ?_⟩
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    by_cases hz : z ∈ U
    · obtain ⟨x, hx, rfl⟩ := hz
      exact Or.inl ⟨x, ball_subset_closedBall hx, (hpatch x (ball_subset_closedBall hx)).symm⟩
    · exact Or.inr ⟨z, hz, (hoff z hz).symm⟩
  · rintro (⟨x, hx, rfl⟩ | ⟨z, hz, rfl⟩)
    · exact ⟨e x, hpatch x hx⟩
    · exact ⟨z, hoff z hz⟩

end Poincare.Manifold.Schoenflies
