import PoincareLib.Topology.Manifold.Smoothing.Rigidity.General.Mathlib.RelativeCoreRetraction
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.General.Mathlib.EmbeddedInverse
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith

/-!
# Connected core after removing one actual boundary collar

Only the selected frontier component is collared. Collapsing its short
closed strip onto the positive end gives a retraction of the entire
connected domain, without assuming a component correspondence.
-/

set_option autoImplicit false
open Set

namespace PoincareMT.M76

theorem partial_boundary_collar_connected_core
    {E X : Type*} [TopologicalSpace E] [Zero E]
    [TopologicalSpace X] [T2Space X]
    {N : Set E} {K : Set X}
    (hK : IsCompact K) (hKc : IsConnected K) (hN : IsCompact N)
    (c : E × ℝ → X) (hc : ContinuousOn c (N ×ˢ Icc (0 : ℝ) 1))
    (hi : Topology.IsEmbedding (fun z : (N ×ˢ Icc (0 : ℝ) 1 : Set (E × ℝ)) => c z))
    (hinside : MapsTo c (N ×ˢ Icc (0 : ℝ) 1) K)
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hopen : IsOpen ((Subtype.val : K → X) ⁻¹' (c '' (N ×ˢ Ico 0 a)))) :
    IsCompact (K \ (c '' (N ×ˢ Ico 0 a))) ∧
      IsConnected (K \ (c '' (N ×ˢ Ico 0 a))) ∧
      (c '' (N ×ˢ Icc 0 a)) ∩ (K \ (c '' (N ×ˢ Ico 0 a))) = c '' (N ×ˢ {a}) ∧
      ∃ r : K → X, Continuous r ∧ range r = K \ (c '' (N ×ˢ Ico 0 a)) ∧
        ∀ x : K, (x : X) ∈ K \ (c '' (N ×ˢ Ico 0 a)) → r x = x := by
  let A := c '' (N ×ˢ Icc 0 a)
  let U := c '' (N ×ˢ Ico 0 a)
  let S := c '' (N ×ˢ {a})
  have hsub : N ×ˢ Icc (0 : ℝ) a ⊆ N ×ˢ Icc 0 1 :=
    fun _ hz => ⟨hz.1,hz.2.1,hz.2.2.trans ha1⟩
  have hAi : IsCompact A := (hN.prod isCompact_Icc).image_of_continuousOn (hc.mono hsub)
  have hAK : A ⊆ K := by rintro _ ⟨z,hz,rfl⟩; exact hinside (hsub hz)
  have hUA : U ⊆ A := image_mono (prod_mono subset_rfl Ico_subset_Icc_self)
  have hinj : InjOn c (N ×ˢ Icc (0 : ℝ) 1) := by
    intro z hz w hw hzw
    exact congrArg Subtype.val (hi.injective (a₁ := ⟨z,hz⟩) (a₂ := ⟨w,hw⟩) hzw)
  have hlevel : A \ U = S := by
    apply Subset.antisymm
    · rintro _ ⟨⟨z,hz,rfl⟩,hn⟩
      have ht : z.2 = a := le_antisymm hz.2.2 (not_lt.mp (fun h => hn ⟨z,⟨hz.1,hz.2.1,h⟩,rfl⟩))
      exact ⟨z,⟨hz.1,ht⟩,rfl⟩
    · rintro _ ⟨z,⟨hzN,hzt⟩,rfl⟩
      have ht : z.2 = a := hzt
      have hz : z ∈ N ×ˢ Icc (0 : ℝ) a := ⟨hzN,by rw [ht]; exact ⟨ha.le,le_rfl⟩⟩
      refine ⟨⟨z,hz,rfl⟩,?_⟩
      rintro ⟨w,hw,hwz⟩
      have hwz' := congrArg Prod.snd (hinj
        (hsub ⟨hw.1,hw.2.1,hw.2.2.le⟩) (hsub hz) hwz)
      linarith [hw.2.2]
  obtain ⟨k,hk,hleft,_,hkbounds⟩ := hi.exists_inverse_on_image
  let r0 : X → X := fun x => c ((k x).1,a)
  have hr0 : ContinuousOn r0 A := by
    apply hc.comp ((hk.mono (image_mono hsub)).fst.prodMk continuousOn_const)
    intro x hx
    exact ⟨(hkbounds (image_mono hsub hx)).1,ha.le,ha1⟩
  have hrmap : MapsTo r0 A S := fun x hx =>
    ⟨((k x).1,a),⟨(hkbounds (image_mono hsub hx)).1,rfl⟩,rfl⟩
  have hrfix : EqOn r0 id S := by
    rintro _ ⟨z,⟨hzN,hzt⟩,rfl⟩
    have ht : z.2 = a := hzt
    have hz : z ∈ N ×ˢ Icc (0 : ℝ) 1 := ⟨hzN,by rw [ht]; exact ⟨ha.le,ha1⟩⟩
    change c ((k (c z)).1,a) = c z
    rw [hleft z hz]
    exact congrArg c (Prod.ext rfl ht.symm)
  obtain ⟨r,hr,hrange,hfix⟩ := exists_relative_core_retraction hAi.isClosed hAK hUA hopen hlevel r0 hr0 hrmap hrfix
  have hcore : IsCompact (K \ U) := by
    obtain ⟨V,hV,hVU⟩ := isOpen_induced_iff.mp hopen
    have hKV : K \ U = K \ V := by
      ext x
      constructor
      · intro hx
        exact ⟨hx.1,fun h => hx.2 ((Set.ext_iff.mp hVU ⟨x,hx.1⟩).mp h)⟩
      · intro hx
        exact ⟨hx.1,fun h => hx.2 ((Set.ext_iff.mp hVU ⟨x,hx.1⟩).mpr h)⟩
    rw [hKV]
    exact hK.diff hV
  have hcconn : IsConnected (K \ U) := by
    let : ConnectedSpace K := isConnected_iff_connectedSpace.mp hKc
    rw [←hrange]
    exact isConnected_range hr
  refine ⟨hcore,hcconn,?_,r,hr,hrange,hfix⟩
  change A ∩ (K \ U) = S
  rw [←hlevel]
  ext x
  exact ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,hAK h.1,h.2⟩⟩

end PoincareMT.M76
