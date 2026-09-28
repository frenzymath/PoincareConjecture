import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.Replacement.RelativeCapPush

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : P2) 1
local notation "Rim" => sphere (0 : P2) 1
local notation "J" => Icc (0 : ℝ) 1

theorem exists_original_finite_cap_push
    {X ι B E : Type*} [MetricSpace X]
    [TopologicalSpace B] [CompactSpace B] [PreconnectedSpace B]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {R S A T Z : Set X}
    (s : ChartwisePLSphere e S) (hR : IsCompact R) (he : PLDomain e R)
    (hSR : S ⊆ interior R) {d r : Set E} (hd : IsFinitePLBallPair P2 d r)
    (j : E → X) (hj : PolyhedralPLInCharts e j d) (hji : InjOn j d)
    (hjS : MapsTo j d S) (hA : IsClosed A) (hT : IsClosed T) (hZ : IsClosed Z)
    (hja : Disjoint (j '' r) A) (hjZ : Disjoint (j '' d) Z)
    (hjT : ∀ x ∈ d, j x ∈ T ↔ x ∈ r)
    (p : B × J → X) (hp : Continuous p)
    (hp0 : ∀ b, p (b,⟨0,by norm_num⟩) ∈ j '' (d \ r))
    (hproper : ∀ z, p z ∈ S ↔ (z.2 : ℝ) = 0)
    (hcover : A ⊆ S ∪ range p ∪ Z) :
    ∃ k : E → X, PolyhedralPLInCharts e k d ∧ InjOn k d ∧
      MapsTo k d (interior R) ∧ EqOn k j r ∧
      Disjoint (k '' d) A ∧ (∀ x ∈ d, k x ∈ T ↔ x ∈ r) := by
  have hD : IsFinitePLBallPair P2 D Rim := by
    have h := CoordinateHalfBoxes.base_ballPair (show (0 : ℝ) < 1 by norm_num)
    have hbase : CoordinateHalfBoxes.base 1 = D := by
      ext x
      simp only [CoordinateHalfBoxes.base,mem_prod,mem_Icc,mem_closedBall,
        dist_zero_right,Prod.norm_def,Real.norm_eq_abs,max_le_iff,abs_le]
    have hfront := h.frontier_eq_of_finrank_eq rfl
    rw [hbase,frontier_closedBall _ one_ne_zero] at hfront
    rwa [hbase,←hfront] at h
  obtain ⟨H,hH,hrim⟩ := hD.exists_homeomorph hd
  have hHinv := hH.symm
  obtain ⟨u,hu,huval⟩ := hH
  obtain ⟨v,hv,hvval⟩ := hHinv
  have humap : MapsTo u D d := by
    intro x hx
    rw [←huval ⟨x,hx⟩]
    exact (H ⟨x,hx⟩).property
  have hvmap : MapsTo v d D := by
    intro x hx
    rw [←hvval ⟨x,hx⟩]
    exact (H.symm ⟨x,hx⟩).property
  have huri (x : P2) (hx : x ∈ D) : u x ∈ r ↔ x ∈ Rim := by
    rw [←huval ⟨x,hx⟩]
    exact (hrim ⟨x,hx⟩).symm
  have hvri (x : E) (hx : x ∈ d) : v x ∈ Rim ↔ x ∈ r := by
    rw [←hvval ⟨x,hx⟩]
    simpa only [H.apply_symm_apply] using (hrim (H.symm ⟨x,hx⟩))
  have huv (x : E) (hx : x ∈ d) : u (v x) = x := by
    rw [←huval ⟨v x,hvmap hx⟩]
    have hvx : (⟨v x,hvmap hx⟩ : D) = H.symm ⟨x,hx⟩ :=
      Subtype.ext (hvval ⟨x,hx⟩).symm
    rw [hvx,H.apply_symm_apply]
  have hui : InjOn u D := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (H.injective (Subtype.ext
      ((huval ⟨x,hx⟩).trans (hxy.trans (huval ⟨y,hy⟩).symm))))
  have hju : PolyhedralPLInCharts e (j ∘ u) D := by
    obtain ⟨L,hL,hLD,hLf⟩ := hu
    rw [←hLD]
    exact hj.comp_finitePiecewiseAffineOn L hL ⟨L,hL,rfl,hLf⟩
      (fun _ hx => humap (hLD.subset hx))
  have hjuA : Disjoint ((j ∘ u) '' Rim) A := by
    apply Set.disjoint_left.mpr
    rintro y ⟨x,hx,rfl⟩ hy
    exact Set.disjoint_left.mp hja
      ⟨u x,(huri x (sphere_subset_closedBall hx)).mpr hx,rfl⟩ hy
  have hjuZ : Disjoint ((j ∘ u) '' D) Z := by
    apply Set.disjoint_left.mpr
    rintro y ⟨x,hx,rfl⟩ hy
    exact Set.disjoint_left.mp hjZ ⟨u x,humap hx,rfl⟩ hy
  have hpu (b : B) : p (b,⟨0,by norm_num⟩) ∈ (j ∘ u) '' ball (0 : P2) 1 := by
    obtain ⟨x,hx,hxp⟩ := hp0 b
    refine ⟨v x,?_,?_⟩
    · have hvD := hvmap hx.1
      have hvnot : v x ∉ Rim := fun h => hx.2 ((hvri x hx.1).mp h)
      rw [mem_ball_zero_iff]
      apply lt_of_le_of_ne (mem_closedBall_zero_iff.mp hvD)
      exact fun h => hvnot (mem_sphere_zero_iff_norm.mpr h)
    · change j (u (v x)) = _
      rw [huv x hx.1]
      exact hxp
  obtain ⟨k,hk,hki,hkR,hkrim,hkA,hkT⟩ := exists_original_relative_cap_push
    s hR he hSR (j ∘ u) hju (hji.comp hui humap)
    (fun _ hx => hjS (humap hx)) hA hT hZ hjuA hjuZ
    (fun x hx => (hjT (u x) (humap hx)).trans (huri x hx)) p hp hpu hproper hcover
  have hkv : PolyhedralPLInCharts e (k ∘ v) d := by
    obtain ⟨L,hL,hLd,hLf⟩ := hv
    rw [←hLd]
    exact hk.comp_finitePiecewiseAffineOn L hL ⟨L,hL,rfl,hLf⟩
      (fun _ hx => hvmap (hLd.subset hx))
  refine ⟨k ∘ v,hkv,?_,fun _ hx => hkR (hvmap hx),?_,?_,?_⟩
  · intro x hx y hy hxy
    have hvxy := hki (hvmap hx) (hvmap hy) hxy
    rw [←huv x hx,←huv y hy,hvxy]
  · intro x hx
    change k (v x) = j x
    rw [hkrim ((hvri x (hd.1 hx)).mpr hx)]
    exact congrArg j (huv x (hd.1 hx))
  · apply Set.disjoint_left.mpr
    rintro y ⟨x,hx,rfl⟩ hy
    exact Set.disjoint_left.mp hkA ⟨v x,hvmap hx,rfl⟩ hy
  · intro x hx
    exact (hkT (v x) (hvmap hx)).trans (hvri x hx)

end PoincareConjecture.M76.Dehn.Annuli
