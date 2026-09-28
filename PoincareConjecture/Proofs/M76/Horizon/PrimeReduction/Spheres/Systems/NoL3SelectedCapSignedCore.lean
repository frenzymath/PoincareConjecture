import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.RelativeCoreRetraction
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.EmbeddedInverse
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith

set_option autoImplicit false
open Set

namespace PoincareConjecture.M76

theorem isConnected_selected_endpoint_inner_remainder
    {E X : Type*} [TopologicalSpace E] [Zero E]
    [TopologicalSpace X] [T2Space X]
    {N : Set E} {K : Set X}
    (hKc : IsConnected K) (hN : IsCompact N)
    (c : E × ℝ → X) (hc : ContinuousOn c (N ×ˢ Icc (-1 : ℝ) 1))
    (hi : Topology.IsEmbedding (fun z : (N ×ˢ Icc (-1 : ℝ) 1 : Set (E × ℝ)) => c z))
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hinside : MapsTo c (N ×ˢ Icc (-a) 0) K)
    (hout : Disjoint (c '' (N ×ˢ Ioo 0 a)) K)
    (hopen : IsOpen (c '' (N ×ˢ Ioo (-a) a))) :
    IsConnected (K \ (c '' (N ×ˢ Ioo (-a) a))) := by
  let A := c '' (N ×ˢ Icc (-a) 0)
  let U := c '' (N ×ˢ Ioc (-a) 0)
  let S := c '' (N ×ˢ {-a})
  let O := c '' (N ×ˢ Ioo (-a) a)
  have hsub : N ×ˢ Icc (-a) (0 : ℝ) ⊆ N ×ˢ Icc (-1) 1 :=
    fun _ hz => ⟨hz.1,by linarith [hz.2.1],by linarith [hz.2.2]⟩
  have hAi : IsCompact A := (hN.prod isCompact_Icc).image_of_continuousOn (hc.mono hsub)
  have hAK : A ⊆ K := by rintro _ ⟨z,hz,rfl⟩; exact hinside hz
  have hUA : U ⊆ A := image_mono (prod_mono subset_rfl Ioc_subset_Icc_self)
  have hinj : InjOn c (N ×ˢ Icc (-1 : ℝ) 1) := by
    intro z hz w hw hzw
    exact congrArg Subtype.val (hi.injective (a₁ := ⟨z,hz⟩) (a₂ := ⟨w,hw⟩) hzw)
  have hrel (x : K) : (x : X) ∈ O ↔ (x : X) ∈ U := by
    constructor
    · rintro ⟨z,hz,hzx⟩
      have ht : z.2 ≤ 0 := by
        by_contra ht
        exact disjoint_left.mp hout ⟨z,⟨hz.1,lt_of_not_ge ht,hz.2.2⟩,hzx⟩ x.property
      exact ⟨z,⟨hz.1,hz.2.1,ht⟩,hzx⟩
    · rintro ⟨z,hz,hzx⟩
      exact ⟨z,⟨hz.1,hz.2.1,by linarith [hz.2.2]⟩,hzx⟩
  have hUopen : IsOpen ((Subtype.val : K → X) ⁻¹' U) := by
    have heq : (Subtype.val : K → X) ⁻¹' U = (Subtype.val : K → X) ⁻¹' O := by
      ext x
      exact (hrel x).symm
    rw [heq]
    exact hopen.preimage continuous_subtype_val
  have hlevel : A \ U = S := by
    apply Subset.antisymm
    · rintro _ ⟨⟨z,hz,rfl⟩,hn⟩
      have ht : z.2 = -a := le_antisymm (not_lt.mp (fun h => hn ⟨z,⟨hz.1,h,hz.2.2⟩,rfl⟩)) hz.2.1
      exact ⟨z,⟨hz.1,ht⟩,rfl⟩
    · rintro _ ⟨z,⟨hzN,hzt⟩,rfl⟩
      have ht : z.2 = -a := hzt
      have hz : z ∈ N ×ˢ Icc (-a) (0 : ℝ) := ⟨hzN,by rw [ht]; exact ⟨le_rfl,by linarith⟩⟩
      refine ⟨⟨z,hz,rfl⟩,?_⟩
      rintro ⟨w,hw,hwz⟩
      have hwz' := congrArg Prod.snd (hinj
        (hsub ⟨hw.1,hw.2.1.le,hw.2.2⟩) (hsub hz) hwz)
      linarith [hw.2.1]
  obtain ⟨k,hk,hleft,_,hkbounds⟩ := hi.exists_inverse_on_image
  let r0 : X → X := fun x => c ((k x).1,-a)
  have hr0 : ContinuousOn r0 A := by
    apply hc.comp ((hk.mono (image_mono hsub)).fst.prodMk continuousOn_const)
    intro x hx
    exact ⟨(hkbounds (image_mono hsub hx)).1,by linarith,by linarith⟩
  have hrmap : MapsTo r0 A S := fun x hx =>
    ⟨((k x).1,-a),⟨(hkbounds (image_mono hsub hx)).1,rfl⟩,rfl⟩
  have hrfix : EqOn r0 id S := by
    rintro _ ⟨z,⟨hzN,hzt⟩,rfl⟩
    have ht : z.2 = -a := hzt
    have hz : z ∈ N ×ˢ Icc (-1 : ℝ) 1 := ⟨hzN,by rw [ht]; constructor <;> linarith⟩
    change c ((k (c z)).1,-a) = c z
    rw [hleft z hz]
    exact congrArg c (Prod.ext rfl ht.symm)
  obtain ⟨r,hr,hrange,_⟩ := exists_relative_core_retraction hAi.isClosed hAK hUA hUopen hlevel r0 hr0 hrmap hrfix
  have heq : K \ O = K \ U := by
    ext x
    exact ⟨fun h => ⟨h.1,fun hx => h.2 ((hrel ⟨x,h.1⟩).mpr hx)⟩,
      fun h => ⟨h.1,fun hx => h.2 ((hrel ⟨x,h.1⟩).mp hx)⟩⟩
  rw [heq,←hrange]
  let : ConnectedSpace K := isConnected_iff_connectedSpace.mp hKc
  exact isConnected_range hr

end PoincareConjecture.M76
