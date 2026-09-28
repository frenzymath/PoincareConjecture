import PoincareConjecture.Proofs.M07.Analysis.Calculus.Diffeomorphism.SmoothCorrection
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Stages.SourceEmbedding
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Stages.SourceEmbedding.Separation
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Stages.SourceEmbedding.ChartContainment











set_option autoImplicit false
open Set Filter Metric Poincare.Gluing Poincare.Analysis.Calculus
open scoped Topology NNReal ContDiff Manifold

namespace PoincareConjecture.ChartDistance

theorem exists_source_embedding_extension
    {d : ℕ} {Q : Type*} [MetricSpace Q]
    {U : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U) [Nonempty U]
    {q : U → Q} (hq : Topology.IsOpenEmbedding q)
    {M : ℕ → Type*} [∀ k, MetricSpace (M k)]
    {e : ∀ k, U → M k} (he : ∀ k, Topology.IsOpenEmbedding (e k))
    {L : ℝ≥0} (hL : ∀ k, LipschitzWith L (e k))
    {c : ℝ} (hc : 0 < c)
    (hlower : ∀ k x y, c * dist x y ≤ dist (e k x) (e k y))
    (hconn : ∀ k (p : M k) r, IsPreconnected (ball p r))
    {V A A' : Set Q} (hV : IsOpen V) (hA : IsCompact A) (hA' : IsCompact A')
    (hAA' : A ⊆ interior A') (hA'V : A' ⊆ V)
    {C : Set U} (hC : IsCompact C) {F : ∀ k, Q → M k}
    (hF : ∀ᶠ k in atTop, Topology.IsOpenEmbedding (fun x : V => F k x))
    (hdist : TendstoUniformlyOn
      (fun k (p : Q × U) => dist (F k p.1) (e k p.2))
      (fun p => dist p.1 (q p.2)) atTop (A' ×ˢ C))
    (hlocal : let u := hU.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph
      let r := fun k y => Subtype.val (Function.invFun (e k) (F k (q (u.symm y))))
      ∀ x ∈ Subtype.val '' (q ⁻¹' V), ∃ W : Set (EuclideanSpace ℝ (Fin d)),
        IsOpen W ∧ x ∈ W ∧ ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (r k) W)
    (hjet : let u := hU.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph
      let r := fun k y => Subtype.val (Function.invFun (e k) (F k (q (u.symm y))))
      ∀ m B, IsCompact B → B ⊆ Subtype.val '' (q ⁻¹' V) → TendstoUniformlyOn
        (fun k => iteratedFDeriv ℝ m (r k)) (iteratedFDeriv ℝ m id) atTop B) :
    ∃ a : ℕ → EuclideanSpace ℝ (Fin d) ≃ₜ EuclideanSpace ℝ (Fin d),
      (∀ m B, IsCompact B → TendstoUniformlyOn
        (fun k => iteratedFDeriv ℝ m (a k)) (iteratedFDeriv ℝ m id) atTop B) ∧
      ∀ᶠ k in atTop, ContDiff ℝ ∞ (a k) ∧ ContDiff ℝ ∞ (a k).symm ∧
        (a k) '' U = U ∧ ∃ G : Q → M k,
          Topology.IsOpenEmbedding (fun x : (interior A ∪ q '' interior C : Set Q) => G x) ∧
          EqOn G (F k) (interior A) ∧
          ∀ y ∈ interior C, G (q y) = e k
            (hU.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph.symm (a k y)) := by
  classical
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  let u := hU.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph
  let r := fun k y => Subtype.val (Function.invFun (e k) (F k (q (u.symm y))))
  let W : Set (EuclideanSpace ℝ (Fin d)) := Subtype.val '' (q ⁻¹' V)
  have hW : IsOpen W := hU.isOpenEmbedding_subtypeVal.isOpenMap _ (hV.preimage hq.continuous)
  let K := C ∩ q ⁻¹' A'
  have hK : IsCompact K := hC.inter_right (hA'.isClosed.preimage hq.continuous)
  have happrox : TendstoUniformlyOn (fun k y => dist (F k (q y)) (e k y))
      (fun _ => 0) atTop K := by
    have h := (hdist.comp (fun y : U => (q y, y))).mono
      (show K ⊆ (fun y : U => (q y, y)) ⁻¹' (A' ×ˢ C) from fun _ hy => ⟨hy.2, hy.1⟩)
    simpa only [Function.comp_def, dist_self] using h
  have hreach := eventually_mem_range_of_uniform_chart_approximation
    hL hc hlower he hconn hK happrox
  have hKW : Subtype.val '' K ⊆ W := by
    rintro _ ⟨y, hy, rfl⟩
    exact mem_image_of_mem Subtype.val (hA'V hy.2)
  obtain ⟨W', S, _, hKW', _, _, hSW, a, ha, hajet⟩ :=
    exists_smooth_relative_correction_sequence hW (hK.image continuous_subtype_val) hKW hlocal hjet
  have hSU : S ⊆ U := hSW.trans (by rintro _ ⟨y, _, rfl⟩; exact y.property)
  have hau : ∀ᶠ k in atTop, (a k) '' U = U := ha.mono fun _ hk => hk.2.2.2.2.2 U hSU
  let b : ℕ → U → U := fun k y => u.symm (a k y)
  have hbval : ∀ᶠ k in atTop, ∀ y : U,
      (b k y : EuclideanSpace ℝ (Fin d)) = a k y := by
    filter_upwards [hau] with k hk y
    have hay : a k y ∈ U := hk.subset ⟨y, y.property, rfl⟩
    exact Topology.IsOpenEmbedding.toOpenPartialHomeomorph_right_inv
      (f := (Subtype.val : U → EuclideanSpace ℝ (Fin d)))
      (h := hU.isOpenEmbedding_subtypeVal) ⟨⟨a k y, hay⟩, rfl⟩
  have hb : TendstoUniformlyOn b id atTop C := by
    have hzero : TendstoUniformlyOn (fun k => (a k : _ → _)) id atTop (Subtype.val '' C) := by
      simpa only [Function.comp_def, iteratedFDeriv_zero_apply] using
        (ContinuousMultilinearMap.uniformContinuous_eval_const
          (0 : Fin 0 → EuclideanSpace ℝ (Fin d))).comp_tendstoUniformlyOn
          (hajet 0 _ (hC.image continuous_subtype_val))
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [hbval, Metric.tendstoUniformlyOn_iff.mp hzero ε hε] with k hk hsmall y hy
    change dist (y : EuclideanSpace ℝ (Fin d)) (b k y : EuclideanSpace ℝ (Fin d)) < ε
    rw [hk y]
    exact hsmall y (mem_image_of_mem Subtype.val hy)
  have hagree : ∀ᶠ k in atTop, ∀ y ∈ C, q y ∈ A' → e k (b k y) = F k (q y) := by
    filter_upwards [ha, hbval, hreach] with k hk hbv hr y hy hyA'
    have hay : a k (y : EuclideanSpace ℝ (Fin d)) = r k y :=
      hk.2.2.1 (hKW' (mem_image_of_mem Subtype.val ⟨hy, hyA'⟩))
    have huy : u.symm (y : EuclideanSpace ℝ (Fin d)) = y :=
      u.left_inv (mem_univ y)
    have hby : b k y = Function.invFun (e k) (F k (q y)) := by
      apply Subtype.ext
      rw [hbv y, hay]
      simp only [r, huy]
    rw [hby]
    exact Function.invFun_eq (hr y ⟨hy, hyA'⟩)
  have hinj : ∀ᶠ k in atTop, InjOn (F k) V := hF.mono fun k hk x hx y hy hxy =>
    congrArg Subtype.val (hk.injective (show F k (⟨x, hx⟩ : V) = F k (⟨y, hy⟩ : V) from hxy))
  have hident := eventually_source_extension_eq_iff hq.continuous hA hC hAA' hA'V
    hinj (tendstoUniformlyOn_corrected_chart_dist hL
      (hdist.mono (prod_mono (hAA'.trans interior_subset) Subset.rfl)) hb) hagree
  refine ⟨a, hajet, ?_⟩
  filter_upwards [ha, hau, hbval, hF, hident] with k hk haku hbv hFk hi
  let bk : U ≃ₜ U := ((a k).image U).trans (Homeomorph.setCongr haku)
  have hbk : (bk : U → U) = b k := by
    funext y
    exact Subtype.ext (hbv y).symm
  have hAV : interior A ⊆ V := interior_subset.trans (hAA'.trans (interior_subset.trans hA'V))
  have hFi : Topology.IsOpenEmbedding (fun x : interior A => F k x) :=
    hFk.comp (.inclusion hAV (isOpen_interior.preimage continuous_subtype_val))
  have hei : Topology.IsOpenEmbedding (fun y : interior C => e k (b k y)) := by
    rw [← hbk]
    exact ((he k).comp bk.isOpenEmbedding).comp isOpen_interior.isOpenEmbedding_subtypeVal
  obtain ⟨G, hG, hleft, hright⟩ := exists_isOpenEmbedding_union_ranges
    (isOpen_interior (s := A)).isOpenEmbedding_subtypeVal
    (hq.comp (isOpen_interior (s := C)).isOpenEmbedding_subtypeVal) hFi hei
    (fun x y => hi x (interior_subset x.property) y (interior_subset y.property))
  let Z := range (Subtype.val : interior A → Q) ∪ range (fun y : interior C => q y)
  let G' : Q → M k := Function.extend (Subtype.val : Z → Q) G (F k)
  have hG' (x : Z) : G' x = G x := Subtype.val_injective.extend_apply G _ x
  have hZ : Z = interior A ∪ q '' interior C := by
    simp only [Z, Subtype.range_coe_subtype, ofPred_mem_eq]
    congr 1
    ext z
    simp only [mem_range, mem_image, Subtype.exists, exists_prop]
  refine ⟨hk.1, hk.2.1, haku, G', ?_, ?_, ?_⟩
  · have hemb : Topology.IsOpenEmbedding (fun x : Z => G' x) := (funext hG').symm ▸ hG
    exact hemb.comp (Homeomorph.setCongr hZ.symm).isOpenEmbedding
  · intro x hx
    exact (hG' ⟨x, Or.inl (mem_range_self (⟨x, hx⟩ : interior A))⟩).trans (hleft ⟨x, hx⟩)
  · intro y hy
    exact (hG' ⟨q y, Or.inr (mem_range_self (⟨y, hy⟩ : interior C))⟩).trans (hright ⟨y, hy⟩)



theorem isLocalDiffeomorphOn_source_extension
    {d : ℕ} {Q M : Type*} [TopologicalSpace Q] [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin d)) Q]
    [ChartedSpace (EuclideanSpace ℝ (Fin d)) M]
    {U : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U) [Nonempty U]
    {q : U → Q} {e : U → M}
    (hq : letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
      IsLocalDiffeomorph (𝓡 d) (𝓡 d) ∞ q)
    (he : letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
      IsLocalDiffeomorph (𝓡 d) (𝓡 d) ∞ e)
    {V A : Set Q} {C : Set U} (hA : IsOpen A) (hC : IsOpen C) (hAV : A ⊆ V)
    {F G : Q → M} (hF : IsLocalDiffeomorphOn (𝓡 d) (𝓡 d) ∞ F V)
    (a : EuclideanSpace ℝ (Fin d) ≃ₜ EuclideanSpace ℝ (Fin d))
    (ha : ContDiff ℝ ∞ a) (hai : ContDiff ℝ ∞ a.symm) (haU : a '' U = U)
    (hleft : EqOn G F A)
    (hright : ∀ y ∈ C, G (q y) = e
      (hU.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph.symm (a y))) :
    IsLocalDiffeomorphOn (𝓡 d) (𝓡 d) ∞ G (A ∪ q '' C) := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let b : U ≃ₜ U := (a.image U).trans (Homeomorph.setCongr haU)
  have hb (y : U) : hU.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph.symm (a y) = b y := by
    have hv : (b y : EuclideanSpace ℝ (Fin d)) = a y := rfl
    rw [← hv]
    exact hU.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph.left_inv (mem_univ (b y))
  let ad : Diffeomorph (𝓡 d) (𝓡 d)
      (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d)) ∞ :=
    { toEquiv := a.toEquiv
      contMDiff_toFun := ha.contMDiff
      contMDiff_invFun := hai.contMDiff }
  have hblocal : IsLocalDiffeomorph (𝓡 d) (𝓡 d) ∞ b := by
    intro y
    have hy := Poincare.isLocalDiffeomorph_subtypeVal (𝓡 d) U hU ∞ y
    have hby := Poincare.isLocalDiffeomorph_subtypeVal (𝓡 d) U hU ∞ (b y)
    have hac := hy.comp (𝓡 d) (EuclideanSpace ℝ (Fin d))
      (ad.isLocalDiffeomorph (y : EuclideanSpace ℝ (Fin d)))
    have hinv : IsLocalDiffeomorphAt (𝓡 d) (𝓡 d) ∞ hby.localInverse (ad y) :=
      hby.localInverse_isLocalDiffeomorphAt
    apply (hac.comp (𝓡 d) U hinv).congr_of_eventuallyEq
    filter_upwards [b.continuous.continuousAt.preimage_mem_nhds
      (hby.localInverse.open_target.mem_nhds hby.localInverse_mem_target)] with z hz
    exact (hby.localInverse_left_inv hz).symm
  rintro ⟨x, hx | ⟨y, hy, rfl⟩⟩
  · apply (hF ⟨x, hAV hx⟩).congr_of_eventuallyEq
    filter_upwards [hA.mem_nhds hx] with z hz
    exact hleft hz
  · apply (hq y).of_comp
    apply ((hblocal y).comp (𝓡 d) M (he (b y))).congr_of_eventuallyEq
    filter_upwards [hC.mem_nhds hy] with z hz
    exact (hright z hz).trans (congrArg e (hb z))

end PoincareConjecture.ChartDistance
