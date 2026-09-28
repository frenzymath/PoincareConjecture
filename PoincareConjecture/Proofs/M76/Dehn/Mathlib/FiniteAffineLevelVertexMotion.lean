import PoincareConjecture.Proofs.M76.Dehn.Mathlib.AffineLevelVertexMotion
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.ProtectedMotionImage
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.PLCarrierMotion










set_option autoImplicit false

open Set unitInterval

namespace Geometry.SimplicialComplex





theorem exists_finite_affine_level_vertex_motion
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (J Q : SimplicialComplex ℝ E) (hJ : J.faces.Finite)
    (hcv : Convex ℝ J.space) (hQJ : Q ≤ J)
    (hfront : frontier J.space ⊆ Q.space)
    (A : AffineSubspace ℝ E)
    (l : List E) (hl : l.Nodup)
    (hvertices : ∀ v ∈ l, v ∈ J.vertices)
    (hverticesA : ∀ v ∈ l, v ∈ A)
    (hfree : ∀ v ∈ l, v ∉ Q.vertices)
    (T : Set E) (hT : T.Finite) (hTA : T ⊆ A)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ H : PLCarrierMotion J.space Q.space ε,
      J.AffineOnFaces (H.map 1) ∧
      (∀ t w, w ∈ J.vertices → w ∉ l → H.map t w = w) ∧
      (∀ t x, H.map t x - x ∈ A.direction) ∧
      ∀ (p : List E) (v : E) (q : List E), l = p ++ v :: q →
        ∀ S : Finset E,
          (S : Set E) ⊆ T ∪ H.map 1 '' {w | w ∈ p} →
          ¬A ≤ affineSpan ℝ (S : Set E) →
          H.map 1 v ∉ affineSpan ℝ (S : Set E) := by
  classical
  induction l generalizing J T ε with
  | nil =>
    refine ⟨PLCarrierMotion.refl J hJ Q.space hε, ?_, ?_, ?_, ?_⟩
    · exact J.affineOnFaces_affine (ContinuousAffineMap.id ℝ E)
    · intro t w _ _
      rfl
    · intro t x
      change x - x ∈ A.direction
      rw [sub_self]
      exact A.direction.zero_mem
    · intro p v q hp
      have hn := congrArg List.length hp
      simp only [List.length_nil, List.length_append, List.length_cons] at hn
      omega
  | cons v l ih =>
    have hnodup := List.nodup_cons.mp hl
    have hv : v ∈ J.vertices := hvertices v (List.mem_cons_self ..)
    have hvA : v ∈ A := hverticesA v (List.mem_cons_self ..)
    have hvQ : v ∉ Q.vertices := hfree v (List.mem_cons_self ..)
    have hhalf : 0 < ε / 2 := half_pos hε
    let B : Finset (Finset E) := hT.toFinset.powerset.filter
      (fun S => ¬A ≤ affineSpan ℝ (S : Set E))
    let Af : B → AffineSubspace ℝ E :=
      fun S => affineSpan ℝ (S.val : Set E)
    have hAf : ∀ i, ¬A ≤ Af i := fun i =>
      (Finset.mem_filter.mp i.property).2
    obtain ⟨F, hFcont, hFinv, hFzero, hFout, hFQ, hFother,
      hFC, hFsmall, hFdir, hFavoid, hFaff⟩ :=
      exists_small_affine_level_vertex_motion J Q hJ hcv hQJ hfront hv hvQ A hvA Af hAf hhalf
    have hfirstAvoid (S : Finset E) (hST : (S : Set E) ⊆ T)
        (hproper : ¬A ≤ affineSpan ℝ (S : Set E)) :
        F 1 v ∉ affineSpan ℝ (S : Set E) := by
      have hSB : S ∈ B := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_powerset.mpr ?_, hproper⟩
        intro x hx
        exact hT.mem_toFinset.mpr (hST hx)
      exact hFavoid ⟨S, hSB⟩
    have htailFix (t : I) (w : E) (hw : w ∈ l) : F t w = w := by
      apply hFother t w (hvertices w (List.mem_cons_of_mem _ hw))
      intro he
      exact hnodup.1 (he ▸ hw)
    have hFlevel (t : I) (x : E) (hx : x ∈ A) : F t x ∈ A := by
      have hd := hFdir t x
      have hm := A.vadd_mem_of_mem_direction hd hx
      simpa only [vsub_eq_sub, vadd_eq_add, sub_add_cancel] using hm
    have hinj : InjOn (F 1) J.space := (F 1).injective.injOn
    let J' := (hFaff 1).embeddedImage hinj
    have hJ' : J'.faces.Finite := (hFaff 1).embeddedImage_finite hinj hJ
    have hspace : J'.space = J.space :=
      ((hFaff 1).embeddedImage_space hinj).trans (hFC 1).1
    have hQJ' : Q ≤ J' :=
      (hFaff 1).protected_le_embeddedImage hinj hQJ (hFQ 1)
    have hcv' : Convex ℝ J'.space := hspace.symm ▸ hcv
    have hfront' : frontier J'.space ⊆ Q.space := hspace.symm ▸ hfront
    have hvertices' (w : E) (hw : w ∈ l) : w ∈ J'.vertices := by
      rw [(hFaff 1).embeddedImage_vertices hinj]
      exact ⟨w, hvertices w (List.mem_cons_of_mem _ hw), htailFix 1 w hw⟩
    have hverticesA' (w : E) (hw : w ∈ l) : w ∈ A :=
      hverticesA w (List.mem_cons_of_mem _ hw)
    have hfree' (w : E) (hw : w ∈ l) : w ∉ Q.vertices :=
      hfree w (List.mem_cons_of_mem _ hw)
    have hTA' : insert (F 1 v) T ⊆ A := by
      intro x hx
      rcases hx with rfl | hx
      · exact hFlevel 1 v hvA
      · exact hTA hx
    obtain ⟨G, hGaff, hGother, hGdir, hGavoid⟩ := ih J' hJ' hcv' hQJ' hfront'
      hnodup.2 hvertices' hverticesA' hfree' (insert (F 1 v) T) (hT.insert _)
        hTA' hhalf
    have hnewVertex : F 1 v ∈ J'.vertices := by
      rw [(hFaff 1).embeddedImage_vertices hinj]
      exact mem_image_of_mem _ hv
    have hnewNotTail : F 1 v ∉ l := by
      intro hm
      have he : v = F 1 v := (F 1).injective (htailFix 1 (F 1 v) hm).symm
      exact hnodup.1 (he.symm ▸ hm)
    have hhead : G.map 1 (F 1 v) = F 1 v :=
      hGother 1 (F 1 v) hnewVertex hnewNotTail
    let F₀ : PLCarrierMotion J.space Q.space (ε / 2) :=
      { map := F
        continuous_map := hFcont
        continuous_symm := hFinv
        zero := hFzero
        outside := hFout
        fixed_protected := hFQ
        carrier := fun t => (hFC t).1
        finitePL := fun t => (hFC t).2
        small := hFsmall }
    let G₀ : PLCarrierMotion J.space Q.space (ε / 2) :=
      { map := G.map
        continuous_map := G.continuous_map
        continuous_symm := G.continuous_symm
        zero := G.zero
        outside := by simpa only [hspace] using G.outside
        fixed_protected := G.fixed_protected
        carrier := by simpa only [hspace] using G.carrier
        finitePL := by
          rw [← hspace]
          exact G.finitePL
        small := G.small }
    rw [show ε = ε / 2 + ε / 2 by ring]
    refine ⟨F₀.trans G₀, ?_, ?_, ?_, ?_⟩
    · exact (hFaff 1).comp_on_embeddedImage hinj hGaff
    · intro t w hw hwl
      have hwv : w ≠ v := by
        intro he
        exact hwl (List.mem_cons.mpr (Or.inl he))
      have hwtail : w ∉ l := fun hm => hwl (List.mem_cons_of_mem _ hm)
      have hw' : w ∈ J'.vertices := by
        rw [(hFaff 1).embeddedImage_vertices hinj]
        exact ⟨w, hw, hFother 1 w hw hwv⟩
      change G.map t (F t w) = w
      rw [hFother t w hw hwv, hGother t w hw' hwtail]
    · intro t x
      have hfx := hFdir t x
      have hgx := hGdir t (F t x)
      change G.map t (F t x) - x ∈ A.direction
      rw [show G.map t (F t x) - x =
        (G.map t (F t x) - F t x) + (F t x - x) by abel]
      exact A.direction.add_mem hgx hfx
    · intro p x q he S hS hproper
      change (S : Set E) ⊆ T ∪ (G.map 1 ∘ F 1) '' {w | w ∈ p} at hS
      change G.map 1 (F 1 x) ∉ affineSpan ℝ (S : Set E)
      cases p with
      | nil =>
        have hx : v = x := (List.cons.inj he).1
        have hST : (S : Set E) ⊆ T := by
          simpa only [List.not_mem_nil, ofPred_false, image_empty, union_empty] using hS
        rw [← hx, hhead]
        exact hfirstAvoid S hST hproper
      | cons u p =>
        have he' : v = u ∧ l = p ++ x :: q := List.cons.inj he
        obtain ⟨rfl, heTail⟩ := he'
        have hp (w : E) (hw : w ∈ p) : w ∈ l := by
          rw [heTail]
          exact List.mem_append_left _ hw
        have hx : x ∈ l := by simp [heTail]
        have hST : (S : Set E) ⊆ insert (F 1 v) T ∪ G.map 1 '' {w | w ∈ p} := by
          intro y hy
          rcases hS hy with hy | ⟨w, hw, hwy⟩
          · exact Or.inl (Or.inr hy)
          · rcases List.mem_cons.mp hw with rfl | hw
            · exact Or.inl (Or.inl (hwy.symm.trans hhead))
            · exact Or.inr ⟨w, hw,
                (congrArg (G.map 1) (htailFix 1 w (hp w hw))).symm.trans hwy⟩
        have hres := hGavoid p x q heTail S hST hproper
        change G.map 1 (F 1 x) ∉ affineSpan ℝ (S : Set E)
        rw [htailFix 1 x hx]
        exact hres

end Geometry.SimplicialComplex
