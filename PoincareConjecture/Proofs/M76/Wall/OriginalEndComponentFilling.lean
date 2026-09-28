import PoincareConjecture.Proofs.M76.Wall.EndComponentFilling
import PoincareConjecture.Proofs.M76.Wall.PLDomainLocalPathConnected

set_option autoImplicit false

open Set

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem exists_original_compact_connected_filling
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R K : Set X}
    (hR : PLDomain e R) (hRconn : IsConnected R)
    (hend : HasOneSimplyConnectedEnd R)
    (hK : IsCompact K) (hKconn : IsConnected K) (hKR : K ⊆ R) :
    ∃ (L : Set X) (x : R), (x : X) ∉ K ∧
      IsCompact L ∧ IsConnected L ∧ K ⊆ L ∧ L ⊆ R ∧
      let U := connectedComponentIn ((Subtype.val : R → X) ⁻¹' K)ᶜ x
      IsOpen U ∧ IsConnected U ∧
        (Subtype.val : R → X) ⁻¹' L = Uᶜ ∧
        frontier ((Subtype.val : R → X) ⁻¹' L) ⊆
          frontier ((Subtype.val : R → X) ⁻¹' K) ∧
        ∀ P : Set X, (Subtype.val : R → X) ⁻¹' P ⊆
            interior ((Subtype.val : R → X) ⁻¹' K) →
          (Subtype.val : R → X) ⁻¹' P ⊆
            interior ((Subtype.val : R → X) ⁻¹' L) := by
  let : ConnectedSpace R := isConnected_iff_connectedSpace.mp hRconn
  let : LocallyPathConnectedSpace R := hR.locallyPathConnectedSpace
  let k : Set R := (Subtype.val : R → X) ⁻¹' K
  have hrange : K ⊆ range (Subtype.val : R → X) := by
    simpa only [Subtype.range_coe] using hKR
  have hk : IsCompact k :=
    Topology.IsInducing.subtypeVal.isCompact_preimage' hK hrange
  have himage : (Subtype.val : R → X) '' k = K :=
    image_preimage_eq_of_subset hrange
  have hkconn : IsConnected k := by
    refine ⟨?_, Topology.IsInducing.subtypeVal.isPreconnected_image.mp ?_⟩
    · obtain ⟨a, ha⟩ := hKconn.nonempty
      exact ⟨⟨a, hKR ha⟩, ha⟩
    · rw [himage]
      exact hKconn.isPreconnected
  obtain ⟨x, hx, hopen, hconn, hkU, hfilled, hfilledconn, hfront, _, _⟩ :=
    hend.exists_compact_connected_filling hk hkconn
  let U := connectedComponentIn kᶜ x
  let L : Set X := (Subtype.val : R → X) '' Uᶜ
  have hpre : (Subtype.val : R → X) ⁻¹' L = Uᶜ := by
    ext y
    constructor
    · rintro ⟨z, hz, hzy⟩
      have heq : z = y := Subtype.ext hzy
      simpa only [heq] using hz
    · intro hy
      exact ⟨y, hy, rfl⟩
  refine ⟨L, x, hx, hfilled.image continuous_subtype_val,
    hfilledconn.image _ continuous_subtype_val.continuousOn, ?_, ?_,
    hopen, hconn, hpre, ?_, ?_⟩
  · intro y hy
    exact ⟨⟨y, hKR hy⟩, hkU hy, rfl⟩
  · rintro y ⟨z, _, rfl⟩
    exact z.property
  · rw [hpre, frontier_compl]
    exact hfront
  · intro P hP
    rw [hpre]
    exact hP.trans (interior_mono hkU)

end PoincareConjecture.M76
