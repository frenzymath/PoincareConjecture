import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Mathlib.LocalPLInvariance
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLComposition
import PoincareConjecture.Proofs.M76.Mathlib.PolyhedralPLInverseChart
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.PolyhedralPLCompatibleChart
import PoincareConjecture.Proofs.M76.Mathlib.AffineHypersurfaceCharts
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonGeometricInputs
import Mathlib.Topology.Covering.Basic

set_option autoImplicit false
open Set Geometry Topology

namespace Geometry

theorem PolyhedralPLInCharts.locallyPiecewiseAffineOn_compatible_chart_comp
    {E F G X ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    [TopologicalSpace X] {e : ι → OpenPartialHomeomorph X F}
    {f : E → X} {S : Set E} (hf : PolyhedralPLInCharts e f S)
    (Q : OpenPartialHomeomorph X F)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid F)
    {g : G → E} {U : Set G} (hg : LocallyPiecewiseAffineOn g U)
    (hgS : MapsTo g U S) (himage : MapsTo (f ∘ g) U Q.source) :
    LocallyPiecewiseAffineOn (Q ∘ f ∘ g) U := by
  intro x hx
  obtain ⟨K, hK, hxK, hKU, hgK⟩ := hg x hx
  have hcomp := hf.comp_finitePiecewiseAffineOn K hK
    (hgK.finitePiecewiseAffineOn hK) (fun y hy => hgS (hKU hy))
  have hfinite := hcomp.finitePiecewiseAffineOn_compatible_chart_finite_source K hK Q hQ
    (fun y hy => himage (hKU hy))
  obtain ⟨J, hJ, hJK, hJF⟩ := hfinite
  exact ⟨J, hJ, hJK.symm ▸ hxK, hJK.subset.trans hKU, hJF⟩

end Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)

private theorem PLDomain.exists_frontier_plane_coordinates
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {N : Set X}
    (he : PLDomain e N) (x : frontier N) :
    ∃ (B : OpenPartialHomeomorph X V3) (a : V2 →ᴬ[ℝ] V3)
      (r : V3 →ᴬ[ℝ] V2) (q : OpenPartialHomeomorph (frontier N) V2),
      x ∈ q.source ∧
      (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid V3) ∧
      q.source = Subtype.val ⁻¹' B.source ∧ q.target = a ⁻¹' B.target ∧
      (∀ y : frontier N, q y = r (B y)) ∧
      ∀ z ∈ q.target, (q.symm z : X) = B.symm (a z) := by
  obtain ⟨ell, v, B, hv, hxB, _, hB, hhalf⟩ := he.halfspace x x.property
  have hell : ell.toAffineMap.linear ≠ 0 := by
    intro hz
    have h := hv
    change ell.toAffineMap.linear v = 1 at h
    rw [hz, LinearMap.zero_apply] at h
    exact zero_ne_one h
  obtain ⟨a, r, hra, har, haz⟩ :=
    ell.toAffineMap.exists_zeroLevel_coordinates (F := V2) hell (by simp)
  obtain ⟨q, hqs, hqt, hq, hqi⟩ := B.exists_affine_hypersurface_chart ell
    (B.isImage_frontier_of_affine_nonneg ell hell hhalf) a r hra har haz x
  exact ⟨B, a, r, q, hqs.symm ▸ hxB, hB, hqs, hqt, hq, hqi⟩

theorem isLocalHomeomorph_frontier_of_polyhedral_model
    {E X Y ι κ : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace X] [TopologicalSpace Y]
    {e : ι → OpenPartialHomeomorph X V3}
    {d : κ → OpenPartialHomeomorph Y V3} {N : Set X} {M : Set Y}
    (he : PLDomain e N) (hd : PLDomain d M)
    {S : Set E} (H : S ≃ₜ frontier N)
    (j : E → X) (hj : PolyhedralPLInCharts e j S)
    (hjval : ∀ z : S, j z = (H z : X))
    (k : E → Y) (hk : PolyhedralPLInCharts d k S)
    (b : C(frontier N, frontier M))
    (hkval : ∀ z : S, k z = (b (H z) : Y))
    (hinj : IsLocallyInjective b) : IsLocalHomeomorph b := by
  classical
  intro x
  obtain ⟨V, hV, hxV, hinjV⟩ := hinj x
  obtain ⟨B, a, r, q, hxq, hB, hqs, hqt, hq, hqi⟩ :=
    he.exists_frontier_plane_coordinates x
  obtain ⟨C, a', r', q', hbxq, hC, hqs', _, hq', _⟩ :=
    hd.exists_frontier_plane_coordinates (b x)
  let W := V ∩ b ⁻¹' q'.source
  have hW : IsOpen W := hV.inter (q'.open_source.preimage b.continuous)
  let U := q.target ∩ q.symm ⁻¹' W
  have hU : IsOpen U := q.symm.continuousOn.isOpen_inter_preimage q.open_target hW
  have hxU : q x ∈ U := ⟨q.map_source hxq, by
    change q.symm (q x) ∈ W
    rw [q.left_inv hxq]
    exact ⟨hxV, hbxq⟩⟩
  let inv : V2 → E := fun z => H.symm (q.symm z)
  have hinv : ContinuousOn inv q.target :=
    (continuous_subtype_val.comp H.symm.continuous).comp_continuousOn q.symm.continuousOn
  have hjinj : InjOn j S := by
    intro z hz w hw hzw
    have hH : H ⟨z, hz⟩ = H ⟨w, hw⟩ := Subtype.ext
      ((hjval ⟨z, hz⟩).symm.trans (hzw.trans (hjval ⟨w, hw⟩)))
    exact congrArg Subtype.val (H.injective hH)
  have hBrev : ∀ i, B.symm.trans (e i) ∈ piecewiseAffineGroupoid V3 := by
    intro i
    simpa only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.symm_symm] using (piecewiseAffineGroupoid V3).symm (hB i)
  have hinvval (z : V2) : j (inv z) = (q.symm z : X) := by
    rw [show inv z = (H.symm (q.symm z) : E) from rfl,
      hjval, H.apply_symm_apply]
  have hinvPL : LocallyPiecewiseAffineOn inv q.target :=
    hj.locallyPiecewiseAffineOn_inverse_comp hjinj B hBrev
      (locallyPiecewiseAffineOn_affine a q.open_target) hinv
      (fun z _ => (H.symm (q.symm z)).property)
      (fun z hz => by simpa only [hqt, mem_preimage] using hz)
      (fun z hz => (hinvval z).trans (hqi z hz))
  have hkval' (z : V2) : k (inv z) = (b (q.symm z) : Y) := by
    change k (H.symm (q.symm z)) = _
    rw [hkval, H.apply_symm_apply]
  have hcoord : LocallyPiecewiseAffineOn (C ∘ k ∘ inv) U :=
    hk.locallyPiecewiseAffineOn_compatible_chart_comp C hC
      (hinvPL.mono hU inter_subset_left)
      (fun z _ => (H.symm (q.symm z)).property) (by
        intro z hz
        change k (inv z) ∈ C.source
        rw [hkval' z]
        simpa only [hqs', mem_preimage] using hz.2.2)
  have hproject := ((locallyPiecewiseAffineOn_affine r' isOpen_univ).comp hcoord).mono hU
    (fun z hz => ⟨hz, mem_univ _⟩)
  have hlocal : LocallyPiecewiseAffineOn (q' ∘ b ∘ q.symm) U := hproject.congr (by
    intro z hz
    change r' (C (k (inv z))) = q' (b (q.symm z))
    rw [hkval' z, hq'])
  have hlocalinj : InjOn (q' ∘ b ∘ q.symm) U := by
    intro z hz w hw hzw
    apply q.symm.injOn hz.1 hw.1
    exact hinjV hz.2.1 hw.2.1 (q'.injOn hz.2.2 hw.2.2 hzw)
  have hLH : IsLocalHomeomorphOn (q' ∘ b ∘ q.symm) U :=
    hlocal.isLocalHomeomorphOn_of_locallyInjective rfl (by
      intro z
      exact ⟨univ, isOpen_univ, mem_univ _, fun y _ w _ heq =>
        Subtype.ext (hlocalinj y.property w.property heq)⟩)
  have hbq : IsLocalHomeomorphOn (b ∘ q.symm) U :=
    hLH.of_comp_left
      ((IsLocalHomeomorphOn.OpenPartialHomeomorph.isLocalHomeomorphOn q').mono (by
        rintro _ ⟨z, hz, rfl⟩
        exact hz.2.2))
      (fun z hz => b.continuous.continuousAt.comp
        (q.symm.continuousAt hz.1))
  have hb := hbq.of_comp_right
    ((IsLocalHomeomorphOn.OpenPartialHomeomorph.isLocalHomeomorphOn q.symm).mono inter_subset_left)
  exact hb x ⟨q x, hxU, q.left_inv hxq⟩

theorem isCoveringMap_frontier_of_polyhedral_model
    {E X Y ι κ : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace X] [TopologicalSpace Y] [T2Space X] [T2Space Y]
    {e : ι → OpenPartialHomeomorph X V3}
    {d : κ → OpenPartialHomeomorph Y V3} {N : Set X} {M : Set Y}
    (he : PLDomain e N) (hd : PLDomain d M) (hN : IsCompact N)
    {S : Set E} (H : S ≃ₜ frontier N)
    (j : E → X) (hj : PolyhedralPLInCharts e j S)
    (hjval : ∀ z : S, j z = (H z : X))
    (k : E → Y) (hk : PolyhedralPLInCharts d k S)
    (b : C(frontier N, frontier M))
    (hkval : ∀ z : S, k z = (b (H z) : Y))
    (hinj : IsLocallyInjective b) : IsCoveringMap b := by
  let : CompactSpace (frontier N) := isCompact_iff_compactSpace.mp
    (hN.of_isClosed_subset isClosed_frontier he.closed.frontier_subset)
  exact isLocalHomeomorph_iff_isCoveringMap.mp
    (isLocalHomeomorph_frontier_of_polyhedral_model he hd H j hj hjval k hk b hkval hinj)

end PoincareConjecture.M76
