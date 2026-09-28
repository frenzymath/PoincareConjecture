import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.SphereCircle.Disks
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Immersion.FiniteDimensional

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : EuclideanSpace Real (Fin 3)) 1
local notation "Iprod" => ModelWithCorners.prod (𝓡 1) 𝓘(Real, Real)

theorem central_circle_geometry_of_tube
    {ε : Real} (hε : 0 < ε) (T : OpenPartialHomeomorph (S1 × Real) S2)
    (hT : ContMDiffOn Iprod (𝓡 2) ∞ T T.source)
    (hTi : ContMDiffOn (𝓡 2) Iprod ∞ T.symm T.target)
    (hsource : T.source = univ ×ˢ Ioo (-ε) ε) :
    let f := fun p : S1 => T (p, 0)
    ContMDiff (𝓡 1) (𝓡 2) ∞ f ∧ Injective f ∧
      ∀ p, Injective (mfderiv (𝓡 1) (𝓡 2) f p) := by
  let f : S1 -> S2 := fun p => T (p, 0)
  let g : S2 -> S1 := fun p => (T.symm p).1
  have h0 (p : S1) : (p, (0 : Real)) ∈ T.source := by
    rw [hsource]
    exact ⟨mem_univ _, by constructor <;> linarith⟩
  have hf : ContMDiff (𝓡 1) (𝓡 2) ∞ f := by
    intro p
    exact (hT.contMDiffAt (T.open_source.mem_nhds (h0 p))).comp p
      ((contMDiff_id.prodMk contMDiff_const) p)
  have hgf : g ∘ f = id := by
    funext p
    change (T.symm (T (p, 0))).1 = p
    rw [T.left_inv (h0 p)]
  refine ⟨hf, (fun p q hpq => congrArg Prod.fst (T.injOn (h0 p) (h0 q) hpq)), ?_⟩
  intro p
  have hg : MDifferentiableAt (𝓡 2) (𝓡 1) g (f p) :=
    (contMDiff_fst.contMDiffAt.comp (f p)
      (hTi.contMDiffAt (T.open_target.mem_nhds (T.map_source (h0 p))))).mdifferentiableAt
        (by simp)
  have hd := mfderiv_comp p hg (hf.mdifferentiable (by simp) p)
  rw [hgf, mfderiv_id] at hd
  intro x y hxy
  have h := congrArg (mfderiv (𝓡 2) (𝓡 1) g (f p)) hxy
  have hx := congrArg (fun L => L x) hd
  have hy := congrArg (fun L => L y) hd
  exact hx.trans (h.trans hy.symm)

theorem exists_inward_disk_of_sphere_tube
    {ε : Real} (hε : 0 < ε) (T : OpenPartialHomeomorph (S1 × Real) S2)
    (hT : ContMDiffOn Iprod (𝓡 2) ∞ T T.source)
    (hTi : ContMDiffOn (𝓡 2) Iprod ∞ T.symm T.target)
    (hsource : T.source = univ ×ˢ Ioo (-ε) ε) :
    ∃ e : OpenPartialHomeomorph E2 S2,
      closedBall 0 1 ⊆ e.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target ∧
      range (fun p : S1 => T (p, 0)) = e '' sphere (0 : E2) 1 ∧
      ∀ p : S1, ∀ t ∈ Ioo (-ε) 0, T (p, t) ∈ e '' ball 0 1 := by
  let C := range (fun p : S1 => T (p, 0))
  obtain ⟨hf, hfi, hfd⟩ := central_circle_geometry_of_tube hε T hT hTi hsource
  obtain ⟨e₀, e₁, hs₀, hs₁, he₀, hei₀, he₁, hei₁, hb₀, hb₁, _, hdis, hcover, _⟩ :=
    exists_sphere_disk_neighborhoods_of_injective_mfderiv hf hfi hfd
  let N := T '' (univ ×ˢ Ioo (-ε) 0)
  have hNs : univ ×ˢ Ioo (-ε) 0 ⊆ T.source := by
    rw [hsource]
    intro z hz
    exact ⟨hz.1, hz.2.1, hz.2.2.trans hε⟩
  have hNc : N ⊆ Cᶜ := by
    rintro y ⟨⟨p, t⟩, ht, rfl⟩ ⟨q, heq⟩
    have h0 : (q, (0 : Real)) ∈ T.source := by
      rw [hsource]
      exact ⟨mem_univ _, by constructor <;> linarith⟩
    have hz := congrArg Prod.snd (T.injOn h0 (hNs ht) heq)
    exact (ne_of_lt ht.2.2) hz.symm
  have hinside (e : OpenPartialHomeomorph E2 S2)
      (hb : e '' sphere (0 : E2) 1 = C) : e '' closedBall 0 1 \ C ⊆ e '' ball 0 1 := by
    rintro y ⟨⟨x, hx, rfl⟩, hy⟩
    refine ⟨x, mem_ball_zero_iff.mpr ?_, rfl⟩
    apply lt_of_le_of_ne (mem_closedBall_zero_iff.mp hx)
    intro heq
    exact hy (hb ▸ mem_image_of_mem e (mem_sphere_zero_iff_norm.mpr heq))
  have hNcover : N ⊆ (e₀ '' ball 0 1) ∪ (e₁ '' ball 0 1) := by
    intro y hy
    have hyall : y ∈ e₀ '' closedBall 0 1 ∪ e₁ '' closedBall 0 1 := hcover ▸ mem_univ y
    rcases hyall with hy₀ | hy₁
    · exact Or.inl (hinside e₀ hb₀ ⟨hy₀, hNc hy⟩)
    · exact Or.inr (hinside e₁ hb₁ ⟨hy₁, hNc hy⟩)
  let : ConnectedSpace S1 := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (E := E2) (by rw [← Module.finrank_eq_rank]; norm_num) 0 zero_le_one)
  have hN : IsPreconnected N := ((isPreconnected_univ.prod isPreconnected_Ioo).image T
    (T.continuousOn.mono hNs))
  have ho₀ := e₀.isOpen_image_of_subset_source isOpen_ball (ball_subset_closedBall.trans hs₀)
  have ho₁ := e₁.isOpen_image_of_subset_source isOpen_ball (ball_subset_closedBall.trans hs₁)
  rcases hN.subset_or_subset ho₀ ho₁ hdis hNcover with hn | hn
  · exact ⟨e₀, hs₀, he₀, hei₀, hb₀.symm,
      fun p t ht => hn ⟨(p, t), ⟨mem_univ _, ht⟩, rfl⟩⟩
  · exact ⟨e₁, hs₁, he₁, hei₁, hb₁.symm,
      fun p t ht => hn ⟨(p, t), ⟨mem_univ _, ht⟩, rfl⟩⟩

end Poincare.Manifold.Schoenflies
