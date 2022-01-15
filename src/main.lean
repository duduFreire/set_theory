import tactic

noncomputable theory

namespace test 

notation `Set` := Type 0
def relation := Set → Set → Prop
constant mem  : relation

instance : has_mem Set Set :=
⟨mem⟩


def fclass := Set → Prop
def is_set (X : fclass) : Prop := ∃(y : Set), ∀(z : Set), z ∈ y ↔ X z 
def proper_class (X : fclass) : Prop := ¬is_set X

def set_of {φ : fclass} (h : is_set φ) : Set := classical.some h
@[simp]lemma mem_set_of (x : Set) {φ : fclass} (h : is_set φ) : x ∈ set_of h ↔ φ x := 
(classical.some_spec h) x

def mem_class (a : Set) (X : fclass) := X a

instance : has_mem Set fclass := ⟨mem_class⟩

lemma existence : nonempty Set := nonempty_of_inhabited


@[ext] axiom extensionality_axiom : ∀(x y : Set), (∀(z : Set), z ∈ x ↔ z ∈ y) → x = y
axiom specification_axiom : 
∀(x : Set) (φ : fclass), ∃(y : Set), ∀(z : Set), z ∈ y ↔ (z ∈ x ∧ φ z)
axiom pairing_axiom : ∀(x y : Set), ∃(z : Set), x ∈ z ∧ y ∈ z
axiom union_axiom : ∀(F : Set), ∃(A : Set), ∀(Y x : Set), Y ∈ F → x ∈ Y → x ∈ A

lemma existence' : ∃(x : Set), true := 
begin 
	cases existence,
	use val,
end

def is_empty (x : Set) : Prop := ∀z, z ∉ x
theorem empty_set_exists : ∃x, is_empty x := 
begin 
	cases existence with x,
	let φ := λz, z ≠ z,
	cases specification_axiom x φ with y hy,
	use y,
	intros z hz,
	specialize hy z,
	rw hy at hz,
	exact not_imp.mpr hz (congr_fun rfl),
end

def empty_set := classical.some empty_set_exists

instance : has_emptyc Set := ⟨empty_set⟩ 

theorem empty_set_is_empty : is_empty ∅ := classical.some_spec empty_set_exists

def empty_set_unique : ∀x, is_empty x ↔ x = ∅ :=
begin 
	intro x,
	split,
	{
		intro h,
		ext,
		split,
		intro hx,
		specialize h z,
		contradiction,


		intro hempty,
		have temp := empty_set_is_empty z,
		contradiction,
	},
	{
		intro h,
		rw h,
		exact empty_set_is_empty,
	},
end

def subset (x y : Set) : Prop := ∀ ⦃z⦄, z ∈ x → z ∈ y
instance : has_subset Set := ⟨subset⟩

lemma subset_iff (x y : Set) : x ⊆ y ↔ ∀ ⦃z⦄, z ∈ x → z ∈ y := by refl

def subset_class (x : Set) (φ : fclass) : Prop := ∀⦃z : Set⦄, z ∈ x → φ z

def transitive (z : Set) : Prop := ∀⦃x⦄, x ∈ z → x ⊆ z
def transitive_class (φ : fclass) := ∀⦃x y: Set⦄, φ x → y ∈ x → φ y

def transitive_rel (z : Set) (R : relation) : Prop := ∀{a b c : Set}, a ∈ z → b ∈ z → c ∈ z →
 R a b → R b c → R a c 
 def transitive_rel_class (φ : fclass) (R : relation) : Prop := ∀{a b c : Set}, φ a → φ b → φ c →
 R a b → R b c → R a c 

def irreflexive (z : Set) (R : relation) : Prop := ∀{x : Set}, x ∈ z → ¬ R x x
def trichotomic (z : Set) (R : relation) : Prop := ∀{a b : Set}, a ∈ z → b ∈ z → R a b ∨ R b a ∨ a = b 
def minimal {z : Set} (R : relation) {x : Set} (hx : x ∈ z) : Prop := ∀⦃y : Set⦄, y ∈ z → ¬ R y x
def well_founded (z : Set) (R : relation) : Prop :=
 ∀{x}, x ⊆ z → x ≠ ∅ → ∃(y : Set) (hy : y ∈ x), minimal R hy

def irreflexive_class (φ : fclass) (R : relation) : Prop := ∀{x : Set}, φ x → ¬ R x x
def trichotomic_class (φ : fclass) (R : relation) : Prop := ∀{a b : Set}, φ a → φ b → R a b ∨ R b a ∨ a = b 
def minimal_class {φ : fclass} (R : relation) {x : Set} (hx : φ x) : Prop := ∀⦃y : Set⦄, φ y → ¬ R y x
def well_founded_class (φ : fclass) (R : relation) : Prop :=
 ∀{x}, subset_class x φ → x ≠ ∅ → ∃(y : Set) (hy : y ∈ x), minimal R hy

structure well_order (set : Set) (R : relation) :=
(irrfl : irreflexive set R)
(tran : transitive_rel set R)
(tri : trichotomic set R)
(wf : well_founded set R)

def is_well_order (x : Set) (R : relation) : Prop := nonempty (well_order x R)

structure well_order_class (φ : fclass) (R : relation) :=
(irrfl : irreflexive_class φ R)
(tran : transitive_rel_class φ R)
(tri : trichotomic_class φ R)
(wf : well_founded_class φ R)

structure ordinal (z : Set) :=
(tran : transitive z)
(wo : well_order z (∈))

structure ordinal_class (φ : fclass) :=
(tran : transitive_class φ)
(wo : well_order_class φ (∈))

lemma wo_set_of_wo_class {φ : fclass} {R : relation} (hwo : well_order_class φ R) (hset : is_set φ)
: well_order (set_of hset) R :=
{
	irrfl := begin
		intros x hx,
		rw mem_set_of at hx,
		exact hwo.irrfl hx,
	end,
	tran := begin 
		intros a b c ha hb hc hab hbc,
		rw mem_set_of at *,
		exact hwo.tran ha hb hc hab hbc,
	end,
	tri := begin 
		intros a b ha hb,
		rw mem_set_of at *,
		exact hwo.tri ha hb,
	end,
	wf := begin 
		intros X hX1 hX2,
		have : subset_class X φ,
		{
			unfold subset_class,
			rw subset_iff at hX1,
			simp at hX1,
			exact hX1,	
		},
		exact hwo.wf this hX2,
	end,
}

lemma ordinal_set_of_ordinal_class {φ : fclass} (hord : ordinal_class φ) (hset : is_set φ) :
ordinal (set_of hset) := 
{
	tran := begin 
		intros x hx y hyx,
		simp at *,
		exact hord.tran hx hyx,
	end,
	wo := wo_set_of_wo_class hord.wo hset
}


@[simp]lemma mem_empty (x : Set) : x ∈ (∅ : Set) ↔ false := iff_false_intro (empty_set_is_empty x)
lemma not_mem_empty {x : Set} (h : x ∈ (∅:Set)) : false := (mem_empty x).mp h

lemma empty_subset : ∀(x : Set), ∅ ⊆ x := 
begin 
	intros x y hy,
	exfalso,
	rw ← mem_empty y,
	exact hy,
end

lemma subset_self (x : Set) : x ⊆ x := λz hz, hz
lemma subset_trans : ∀ {x y z : Set}, x ⊆ y → y ⊆ z → x ⊆ z :=
begin 
	intros x y z hxy hyz w hw,
	exact hyz (hxy hw),
end

theorem eq_iff_subsets (x y : Set) : x = y ↔ x ⊆ y ∧ y ⊆ x := 
begin 
	split,
	{
		intro h,
		split; 
		rw h, 
		exact subset_self y,
		exact subset_self y,
	},
	intro h,
	ext,
	split,
	{
		intro hz,
		exact h.1 hz,
	},
	{
		intro hz,
		exact h.2 hz,
	},
end

lemma subset_empty_iff (x : Set) : x ⊆ ∅ ↔ x = ∅ :=
begin 
	split,
	{
		intro h,
		rw eq_iff_subsets,
		split, exact h,
		exact empty_subset x,
	},
	{
		intro h,
		rw h,
		exact subset_self ∅,
	},
end


lemma empty_is_ordinal : ordinal ∅ := {
	tran := begin 
			intros x hx,
			exfalso,
			rw ← mem_empty x,
			exact hx,
	end,
	wo := {
		irrfl := begin 
				intros x hx,
				exfalso,
				rw ← mem_empty x,
				exact hx,
		end,
		tran := begin 
				intros a b c ha,
				exfalso,
				rw ← mem_empty a,
				exact ha,
		end,
		tri := begin 
				intros a b ha,
				exfalso,
				rw ← mem_empty a,
				exact ha,
		end,
		wf := begin 
			intros a ha ha_nonempty,
			exfalso,
			rw subset_empty_iff a at ha,
			exact ha_nonempty ha,
		end,
	},
}

def ON : fclass := λx, nonempty (ordinal x)
theorem empty_set_is_ordinal : ∅ ∈ ON := nonempty.intro empty_is_ordinal

def univ : fclass := λx, true 
theorem univ_is_proper_class : proper_class univ := 
begin 
	intro h,
	cases h with V hV,
	cases specification_axiom V (λx, x ∉ x) with R hR,
	specialize hR R,
	rw hV R at hR,
	unfold univ at hR,
	simp at hR,
	exact hR,
end

def sep (p : fclass) (s : Set) : Set :=
classical.some (specification_axiom s p)

instance : has_sep Set Set :=
⟨sep⟩

def subclass_set (φ : fclass) (x : Set) := ∀⦃y⦄, φ y → y ∈ x

theorem subclass_of_set_is_set {φ : fclass} {x : Set} (h : subclass_set φ x) :
 is_set φ := 
begin 
	cases specification_axiom x φ with y hy,
	use y,
	intros z,
	specialize hy z,
	rw hy,
	split,
	{
		intro h1,
		exact h1.2,
	},
	{
		intro h1,
		split,
		exact h h1,
		exact h1,
	},
end

lemma pair_set_exists (x y : Set) : ∃(z : Set), ∀w, w ∈ z ↔ w = x ∨ w = y := 
begin 
	cases pairing_axiom x y with k hk,
	have h : subclass_set (λn, n = x ∨ n = y) k,
	{
		intros n hn,
		cases hn,
		rw hn,
		exact hk.1,

		rw hn,
		exact hk.2
	},

	cases subclass_of_set_is_set h with P hP,
	use P,
	simp at hP,
	exact hP,
end

def pair_set (x y : Set) : Set := classical.some (pair_set_exists x y)

lemma pair_set_is_pair (x y : Set) : ∀w, w ∈ (pair_set x y) ↔ w = x ∨ w = y := 
classical.some_spec (pair_set_exists x y)

@[simp]lemma mem_pair (z x y: Set) : z ∈ pair_set x y ↔ z = x ∨ z = y := pair_set_is_pair x y z

def sing (x : Set) := pair_set x x
@[simp]lemma mem_sing (y x : Set) : y ∈ sing x ↔ y = x := 
begin
	unfold sing,
	rw mem_pair,
	exact or_self (y = x),
end

lemma sing_is_sing (x : Set) : ∀y, y ∈ sing x ↔ y = x := λy : Set, mem_sing y x

lemma sing_unique (x y : Set) : (∀z, z ∈ y ↔ z = x) → y = sing x := 
begin 
	intro h,
	ext,
	rw mem_sing,
	exact h z,
end

theorem union_exists (F : Set) : ∃(A : Set), ∀x, x ∈ A ↔ ∃Y ∈ F, x ∈ Y :=
begin
	cases union_axiom F with B hB,
	have h : subclass_set (λx, ∃Y ∈ F, x ∈ Y) B,
	{
		intros x hx,
		cases hx with Y hY,
		cases hY with hY hxY,
		exact hB Y x hY hxY,
	},
	cases subclass_of_set_is_set h with A hA,
	use A,
	simp at hA,
	intros x,
	rw hA x,
	exact bex_def.symm,
end


def union (F : Set) := classical.some (union_exists F)
lemma union_is_union (F : Set) : ∀x, x ∈ union F ↔ ∃Y ∈ F, x ∈ Y :=
classical.some_spec (union_exists F)

@[simp] lemma mem_union (x F : Set) : x ∈ union F ↔ ∃Y ∈ F, x ∈ Y := union_is_union F x

def pair_union (a b : Set) : Set :=
union (pair_set a b)

instance : has_union Set :=
⟨pair_union⟩

@[simp]lemma mem_pair_union (x a b : Set) : x ∈ a ∪ b ↔ x ∈ a ∨ x ∈ b :=
begin 
	unfold has_union.union,
	unfold pair_union,
	rw mem_union,
	split,
	{
		intro h,
		rcases h with ⟨Y, hY, hxY⟩,
		rw mem_pair at hY,
		cases hY,
		{
			left,
			rw ← hY,
			exact hxY
		},
		{
			right,
			rw ← hY,
			exact hxY,
		},
	},
	{
		intros h,
		cases h,
		{
			use a,
			rw mem_pair,
			simp,
			exact h,
		},
		{
			use b,
			rw mem_pair,
			simp,
			exact h,
		},
	},
end

def pair_inter (a b : Set) : Set := classical.some (specification_axiom (a ∪ b) (λz, z ∈ a ∧ z ∈ b))
instance : has_inter Set :=
⟨pair_inter⟩

@[simp]lemma mem_pair_inter (x a b : Set) : x ∈ a ∩ b ↔ x ∈ a ∧ x ∈ b := 
begin 
	unfold has_inter.inter,
	unfold pair_inter,
	have := classical.some_spec (specification_axiom (a ∪ b) (λz, z ∈ a ∧ z ∈ b)),
	specialize this x,
	finish,
end

lemma pair_inter_subset_left (a b : Set) : (a ∩ b) ⊆ a := 
begin 
	intros x hx,
	rw mem_pair_inter at hx,
	exact hx.1,
end

lemma pair_inter_subset_right (a b : Set) : (a ∩ b) ⊆ b := 
begin 
	intros x hx,
	rw mem_pair_inter at hx,
	exact hx.2,
end

lemma pair_inter_symm (a b : Set) : a ∩ b = b ∩ a := 
begin 
	ext,
	split,
	repeat {
		intro z,
		simp at *,
		exact and.comm.mp z,
	},
end

lemma eq_pair_inter_left_iff (a b : Set) : a ∩ b = a ↔ a ⊆ b :=
begin 
	split,
	{
		intro h,
		rw ← h,
		exact pair_inter_subset_right a b, 
	},
	{
		intro h,
		ext,
		split,
		{
			intro hz,
			rw mem_pair_inter at hz,
			exact hz.1,
		},
		{
			intro hz,
			rw mem_pair_inter,
			exact ⟨hz, h hz⟩,
		},
	}
end

lemma eq_pair_inter_right_iff (a b : Set) : a ∩ b = b ↔ b ⊆ a :=
begin 
	rw pair_inter_symm a b,
	exact eq_pair_inter_left_iff b a,
end

def succ (x : Set) : Set := x ∪ sing x
@[simp]lemma mem_succ (y x : Set) : y ∈ succ x ↔ y ∈ x ∨ y = x := 
begin
	unfold succ,
	simp,
end

instance : has_lt Set := ⟨λ s t, s ∈ t⟩
instance : has_le Set := ⟨λ s t, s ∈ t ∨ s = t⟩

@[simp]lemma le_iff (a b : Set) : a ≤ b ↔ a ∈ b ∨ a = b := by refl

lemma lt_succ_self (x : Set) : x < succ x := 
begin 
	unfold has_lt.lt,
	simp,
end

lemma subset_of_wo_is_wo {x y : Set} {R : relation} (hxy : x ⊆ y) (hy : well_order y R) : 
is_well_order x R := 
begin
	have hx : well_order x R := {
		irrfl := λz hz, hy.irrfl (hxy hz),
		tran := λa b c ha hb hc hab hbc, hy.tran (hxy ha) (hxy hb) (hxy hc) hab hbc,
		tri := λ a b hax hbx,hy.tri (hxy hax) (hxy hbx),
		wf := λz hzx hz_nonempty, hy.wf (subset_trans hzx hxy) hz_nonempty,
	},

	exact nonempty.intro hx,
end

lemma ord_not_mem_self {x : Set} (hx : ON x) : x ∉ x := 
begin 
	by_contra h,
	unfold ON at hx,
	cases hx,
	exact hx.wo.irrfl h h,
end

lemma ON_is_transitive : transitive_class ON :=
begin 
	intros x y hx hyx,
	cases hx with x_ord,

	have y_sub_x : y ⊆ x := x_ord.tran hyx,
	cases subset_of_wo_is_wo y_sub_x x_ord.wo with y_wo,

	have hy_is_on : ordinal y := {
		tran := begin 
			intros a hay z hza,
			have hax := x_ord.tran hyx hay,
			have hzx := x_ord.tran hax hza,
			exact x_ord.wo.tran hzx hax hyx hza hay,
		end,
		wo := y_wo,
	},

	exact nonempty.intro hy_is_on,
end

lemma mem_of_ordinal_is_ordinal {x y: Set} (hx : x ∈ ON) (hyx : y ∈ x) : ON y :=
ON_is_transitive hx hyx

lemma diff_exists (x y : Set) : ∃(z : Set), ∀a, a ∈ z ↔ (a ∈ x ∧ a ∉ y) := specification_axiom x (λa, a ∉ y)

def diff (x y : Set) : Set := classical.some (diff_exists x y)

instance : has_sdiff Set :=
⟨diff⟩

@[simp]lemma mem_diff (z x y : Set) : z ∈ x \ y ↔ z ∈ x ∧ z ∉ y := classical.some_spec (diff_exists x y) z
lemma in_diff {z x y : Set} : z ∈ x → z ∉ y → z ∈ x \ y := 
begin 
	intros h1 h2,
	simp,
	exact ⟨h1, h2⟩,
end

lemma nonempty_has_mem {x : Set} (h : x ≠ ∅) : ∃y, y ∈ x := 
begin 
	by_contra h2,
	push_neg at h2,
	have := empty_set_unique x,
	unfold is_empty at this,
	rw this at h2,
	exact h h2,
end

lemma diff_subset (x y : Set) : x \ y ⊆ x := begin 
	intros z hz,
	simp at hz,
	exact hz.1,
end

lemma pair_inter_ordinal {a b : Set} (ha : ordinal a) (hb : ordinal b) : ordinal (a ∩ b) :=
{
	tran := begin 
		intros x hx z hzx,
		simp at *,
		exact ⟨ha.tran hx.1 hzx, hb.tran hx.2 hzx⟩,
	end,
	wo := begin 
		have := subset_of_wo_is_wo (pair_inter_subset_left a b) ha.wo,
		unfold is_well_order at this,
		exact classical.some (classical.exists_true_of_nonempty this),
	end
}

lemma not_rel_min {X x y : Set} {R : relation} {hxX : x ∈ X} (hx_min : minimal R hxX) (hy : R y x)
 : y ∉ X := λh, hx_min h hy

lemma ord_le_iff_subset {x y : Set} (x_ord : ON x) (y_ord : ON y) : x ⊆ y ↔ x ≤ y :=
begin 
	tactic.unfreeze_local_instances,
	cases x_ord,
	cases y_ord,
	split,
	{
		intro h,

		let X := y \ x,
		by_cases X_nonempty : X ≠ ∅,
		{
			left,
			rcases y_ord.wo.wf (diff_subset y x) X_nonempty with ⟨ξ, hξ_diff, hξ_min⟩,
			have hξy : ξ ∈ y := (diff_subset y x) hξ_diff,

			suffices hξ_is_x : ξ = x,{rw ← hξ_is_x, exact hξy},
			rw eq_iff_subsets, split,
			{
				intros μ hμ,
				by_contra hμ_not_in_x,
				apply not_rel_min hξ_min hμ,
				simp,
				exact ⟨y_ord.tran hξy hμ, hμ_not_in_x⟩,
			},
			{
				by_contra h_contra,
				rw subset_iff at h_contra,
				push_neg at h_contra,
				rcases h_contra with ⟨μ, hμx, hμ_notξ⟩,
				have hμy := h hμx,
				have h_or : μ = ξ ∨ ξ ∈ μ,
				{
					have := y_ord.wo.tri hξy hμy,
					tauto,
				},
				cases h_or,
				{
					rw mem_diff at hξ_diff,
					rw h_or at hμx,
					exact hξ_diff.2 hμx,
				},
				have := x_ord.tran hμx h_or,
				rw mem_diff at hξ_diff,
				exact hξ_diff.2 this,
			},
		},
		{
			simp at X_nonempty,
			right,
			rw eq_iff_subsets, split, exact h,
			intros z hzy,
			by_contra hzx,
			have contra := in_diff hzy hzx,
			have : z ∈ X := contra,
			rw X_nonempty at this,
			simp at this, exact this,
		},
	},
	{
		intro h,
		cases h,
		exact y_ord.tran h,

		rw h,
		exact subset_self y,
	},
end

theorem ON_ordinal_class : ordinal_class ON :=
{
	tran := ON_is_transitive,
	wo := 
	{
		irrfl := λx hx, ord_not_mem_self hx,
		tran := begin 
			intros a b c ha hb hc hab hbc,
			cases hc,
			exact hc.tran hbc hab,
		end,
		tri := begin
			intros a b ha hb,
			cases ha,
			cases hb,

			have hinter := pair_inter_ordinal ha hb,
			have hinter_a := pair_inter_subset_left a b,
			have hinter_b := pair_inter_subset_right a b,
			
			rw ord_le_iff_subset (nonempty.intro hinter) (nonempty.intro ha) at hinter_a,
			rw ord_le_iff_subset (nonempty.intro hinter) (nonempty.intro hb) at hinter_b,
			simp at *,
			by_cases a ∩ b = a ∨ a ∩ b = b,
			{
				rw eq_pair_inter_left_iff a b at h,
				rw eq_pair_inter_right_iff a b at h,
				cases h,
				{
					rw ord_le_iff_subset (nonempty.intro ha) (nonempty.intro hb) at h,
					rw le_iff at h,
					finish,
				},
				{
					rw ord_le_iff_subset (nonempty.intro hb) (nonempty.intro ha) at h,
					rw le_iff at h,
					finish,
				},
			},
			push_neg at h,
			have : a ∩ b ∈ a ∧ a ∩ b ∈ b := by finish,
			rw ← mem_pair_inter (a ∩ b) a b at this,
			exfalso,
			exact ord_not_mem_self (nonempty.intro hinter) this,
		end,
		wf := begin 
			intros X hX1 hX2,
			cases nonempty_has_mem hX2 with a ha,
			by_cases a ∩ X = ∅,
			{
				use a,
				use ha,
				intros x hxX hxa,
				have : x ∈ a ∩ X, {rw mem_pair_inter, exact ⟨hxa, hxX⟩,},
				rw h at this,
				exact (mem_empty x).mp this,
			},
			{
				have a_ord : ordinal a,
				{
					have := (hX1 ha),
					unfold ON at this,
					exact classical.some (classical.exists_true_of_nonempty this),
				},
				have h_wo := subset_of_wo_is_wo (pair_inter_subset_left a X) a_ord.wo,
				cases h_wo,
				rcases h_wo.wf (subset_self (a ∩ X)) h with ⟨ξ, hξaX, hξ_min⟩,
				use ξ,
				rw mem_pair_inter at hξaX,
				use hξaX.2,
				
				intros b hbX hbξ,
				have hba := a_ord.tran hξaX.1 hbξ,
				have hbaX : b ∈ a ∩ X, {rw mem_pair_inter at *, exact ⟨hba, hbX⟩},

				exact hξ_min hbaX hbξ,
			},
		end,
	}
}

theorem ON_is_proper_class : proper_class ON :=
begin 
	intro h,
	have h_ord := ordinal_set_of_ordinal_class ON_ordinal_class h,
	have : set_of h ∈ set_of h,
	{
		rw mem_set_of,
		exact nonempty.intro h_ord,
	},

	exact ord_not_mem_self (nonempty.intro h_ord) this,
end

theorem mem_ord_is_ord {x y : Set}  (y_ord : ordinal y) (h : x ∈ y) : ordinal x :=
classical.some (classical.exists_true_of_nonempty (ON_is_transitive (nonempty.intro y_ord) h))

theorem succ_of_ordinal_is_ordinal {z : Set} (h : ordinal z) : ordinal (succ z) := {
	tran := begin
		intros x hx y hy,
		
		simp at *,
		cases hx,
		{
			left,
			exact h.tran hx hy,
		},
		{
			left,
			rw ← hx,
			exact hy,
		},
	end,
	wo := {
		irrfl := begin 
			intros x hxSz hxx,
			rw mem_succ at hxSz,
			cases hxSz,
			{exact (mem_ord_is_ord h hxSz).wo.irrfl hxx hxx},
			{
				rw hxSz at hxx,
				exact ord_not_mem_self (nonempty.intro h) hxx,
			}
		end,
		tran := begin 
			intros a b c ha hb hc hab hbc,
			rw mem_succ at *,
			cases hc,
			{
				have c_ord := mem_ord_is_ord h hc,
				have hbz := h.tran hc hbc,
				exact c_ord.tran hbc hab,
			},
			{
				rw hc at *,
				exact h.tran hbc hab,
			},
		end,
		tri := begin 
			intros a b ha hb,
			rw mem_succ at *,
			cases hb,
			{
				cases ha,
				{exact h.wo.tri ha hb},
				{rw ha, right,left, exact hb},
			},
			{
				rw hb,
				finish,
			},
		end,
		wf := begin 
			intros X hX1 hX2,
			by_cases h_empty : X \ sing z = ∅,
			{
				use z,
				have hX_singz: X = sing z,
				{
					ext k,
					split,
					{
						intro hk,
						rw mem_sing,
						by_contra hh,
						have hknz : k ∉ sing z, {intro hkz, rw mem_sing at hkz, exact hh hkz},
						have : k ∈ (X \ sing z), {rw mem_diff, exact ⟨hk, hknz⟩},
						rw h_empty at this,
						exact (mem_empty k).mp this,
					},
					{
						intro hk, rw mem_sing at hk,
						have : ∀t, t ∈ X → t = z,
						{
							intros t ht,
							by_contra htz,
							have : t ∉ sing z, {intro temp, rw mem_sing at temp, exact htz temp},
							have contra : t ∈ X \ sing z, {rw mem_diff, exact ⟨ht, this⟩},
							rw h_empty at contra,
							exact (mem_empty t).mp contra,
						},
						cases nonempty_has_mem hX2 with α hα,
						specialize this α hα,
						rw hk,
						rw ← this,
						exact hα,
					},
				},
				have hz : z ∈ X, {rw hX_singz, simp,},
				use hz,
				intros a haX haz,
				rw hX_singz at *, simp at *,
				rw haX at haz,
				exact ord_not_mem_self (nonempty.intro h) haz,
			},
			{
				have hX_ss : X \ sing z ⊆ z,
				{
					intros t ht,
					simp at ht,
					specialize hX1 ht.1,
					rw mem_succ at hX1,
					tauto,
				},

				rcases h.wo.wf hX_ss h_empty with ⟨ξ, hξ_in, hξ_min⟩,
				use ξ,
				rw mem_diff at hξ_in,
				use hξ_in.1,

				intros t htX hcontra,
				specialize hX1 hξ_in.1, rw mem_succ at hX1,
				have ht : t ∈ X \ sing z,
				{
					rw mem_diff, use htX,
					intro temp, rw mem_sing at temp,
					cases hX1,

					rw temp at hcontra,
					exact ord_not_mem_self (nonempty.intro h) (h.tran hX1 hcontra),

					rw temp at hcontra,
					rw hX1 at hcontra,
					exact ord_not_mem_self (nonempty.intro h) hcontra,
				},
				exact hξ_min ht hcontra,
			},
		end,
	}
}

lemma not_ord_mem_ord {x y : Set} (x_ord : ordinal x) : x ∈ y → y ∈ x → false :=
λhxy hyx, ord_not_mem_self (nonempty.intro x_ord) (x_ord.tran hyx hxy)

lemma succ_inj_on_ON {x y : Set} (x_ord : ordinal x) (h : succ x = succ y) : x = y :=
begin 
	have hx := lt_succ_self x,
	have hy := lt_succ_self y,
	unfold has_lt.lt at *,
	rw h at hx,
	rw ← h at hy,
	rw mem_succ at *,
	by_cases hx_eq_y : x = y, exact hx_eq_y,
	exfalso,

	have hxy : x ∈ y := by tauto!,
	exact not_ord_mem_ord x_ord hxy (by tauto!),
end

def is_successor {x : Set} (x_ord : ordinal x) : Prop := ∃{y : Set} (hy : ordinal y), x = succ y
def is_limit {x : Set} (x_ord : ordinal x) : Prop := x ≠ ∅ ∧ ¬is_successor x_ord

def nat : fclass := λx, x ∈ ON ∧ ∀⦃y : Set⦄ (y_ord : ordinal y), y ≤ x → y = ∅ ∨ is_successor y_ord

lemma empty_is_nat : ∅ ∈ nat := 
begin 
	split, exact empty_set_is_ordinal,
	intros y y_ord h,
	rw le_iff at h,
	cases h,
	{
		exfalso,
		exact not_mem_empty h,
	},
	{exact or.inl h},
end

lemma le_self (x : Set) : x ≤ x := or.inr rfl

lemma le_tran {x y z : Set} (x_ord : ordinal x) (y_ord : ordinal y) (z_ord : ordinal z)
 (hxy : x ≤ y) (hyz : y ≤ z) : x ≤ z :=
begin
	cases hyz,
	{
		cases hxy,
		{
			left,
			exact z_ord.tran hyz hxy,
		},
		{
			left,
			rw hxy,
			exact hyz,
		},
	},
	{
		rw ← hyz,
		exact hxy,
	},
end

lemma ord_of_mem_ON {x : Set} (h : x ∈ ON) : ordinal x :=
classical.some (classical.exists_true_of_nonempty h)

lemma mem_ON_of_ord {x : Set} (x_ord : ordinal x) : x ∈ ON := nonempty.intro x_ord

lemma nat_is_ord {x : Set} (x_nat : x ∈ nat) : ordinal x := ord_of_mem_ON x_nat.1

lemma mem_of_nat_is_nat {x y : Set} (x_nat : x ∈ nat) (hyx : y ∈ x) : y ∈ nat :=
begin 
	have x_ord := nat_is_ord x_nat,
	have hy_ord := mem_of_ordinal_is_ordinal (nonempty.intro x_ord) hyx,
	have y_ord := ord_of_mem_ON hy_ord,

	split, 
	{exact hy_ord},
	{
		intros z z_ord hz_le_y,
		have hy_le_x : y ≤ x := or.inl hyx,
		have z_le_x : z ≤ x := le_tran z_ord y_ord x_ord hz_le_y hy_le_x,
		cases x_nat with __ hx,
		exact hx z_ord z_le_x
	}
end

lemma succ_of_nat_is_nat {x : Set} (x_nat : x ∈ nat) : succ x ∈ nat :=
begin
	have x_ord := (ord_of_mem_ON x_nat.1),
	split,
	{exact nonempty.intro (succ_of_ordinal_is_ordinal x_ord)},
	{
		intros y y_ord hyx,
		cases hyx,
		{
			rw mem_succ at hyx,
			cases hyx,
			{
				exact (mem_of_nat_is_nat x_nat hyx).2 y_ord (le_self y),
			},
			{
				cases x_nat.2 x_ord (le_self x),
				left, exact (rfl.congr h).mp hyx,
				right,
				rcases h with ⟨a, a_ord, ha⟩,
				use a,
				use a_ord,
				exact (rfl.congr ha).mp hyx, 
			},
		},
		{
			right,
			use x,
			use ord_of_mem_ON x_nat.1,
			exact hyx,
		},
	}
end

def is_inductive (x : Set) : Prop := ∅ ∈ x ∧ ∀⦃y⦄, y ∈ x → succ y ∈ x
def inductive_class (φ : fclass) : Prop := ∅ ∈ φ ∧ ∀⦃y⦄, y ∈ φ → succ y ∈ φ

lemma non_zero_nat_is_succ {x : Set} (x_nat : x ∈ nat) : x ≠ ∅ → 
is_successor (ord_of_mem_ON x_nat.1) :=
begin 
	intro h,
	cases x_nat with x_ord hx,
	specialize hx (ord_of_mem_ON x_ord) (le_self x),
	have : is_successor (ord_of_mem_ON x_ord) := by tauto!,
	rcases this with ⟨a, a_ord, ha⟩,
	use a,
	use a_ord,
	exact ha,
end

theorem inductive_class_contains_nat {I : fclass} (hI : inductive_class I) : ∀⦃x⦄, x ∈ nat → x ∈ I :=
begin 
	intros x x_nat,
	by_contra h,
	have temp : is_set (λz, z ∈ succ x ∧ z ∉ I),
	{
		apply @subclass_of_set_is_set (λz, z ∈ succ x ∧ z ∉ I) (succ x),
		intros y hy, exact hy.1,
	},
	cases temp with X hX, dsimp at hX,
	have X_nonempty : X ≠ ∅,
	{
		intro contra,
		specialize hX x,
		have := hX.mpr ⟨lt_succ_self x, h⟩,
		rw contra at this,
		exact (mem_empty x).mp this,
	},
	have X_ord_set : subset_class X ON,
	{
		intros y hyX,
		rw hX y at hyX,
		have := mem_of_nat_is_nat (succ_of_nat_is_nat x_nat) hyX.1,
		exact nonempty.intro (nat_is_ord this),
	},

	rcases ON_ordinal_class.wo.wf X_ord_set X_nonempty with ⟨n, hnX, hn_min⟩,
	have n_ord := ord_of_mem_ON (X_ord_set hnX),
	have n_nat : n ∈ nat,
	{
		rw hX n at hnX,
		have succ_ord := succ_of_nat_is_nat x_nat,
		exact mem_of_nat_is_nat succ_ord hnX.1,
	},
	have : n ≠ ∅ ∧ ¬is_successor n_ord,
	{
		split,
		{
			intro contra,
			rw contra at hnX,
			rw hX ∅ at hnX,
			exact hnX.2 hI.1,
		},
		{
			intro contra,
			rcases contra with ⟨m, m_ord, hm⟩,
			by_cases hmI : m ∈ I,
			{
				have := hI.2 hmI,
				rw← hm at this,
				rw hX n at hnX,
				exact hnX.2 this,
			},
			{
				have hmSm := lt_succ_self m,
				rw← hm at hmSm,
				have hSx_ord := nat_is_ord (succ_of_nat_is_nat x_nat),
				rw hX n at hnX,
				have := hSx_ord.tran hnX.1 hmSm,
				have hmX : m ∈ X,
				{
					rw hX m,
					exact ⟨this, hmI⟩,
				},
				exact (hn_min hmX) hmSm,
			},
		},
	},
	have contra := non_zero_nat_is_succ n_nat this.1,
	exact this.2 contra,
end

theorem inductive_set_contains_nat {I : Set} (hI : is_inductive I) : subclass_set nat I :=
begin 
	let φ : fclass := λx, x ∈ I,
	have hφ : inductive_class φ,
	{
		split,
		{exact hI.1},
		{
			intros y hy,
			exact hI.2 hy,
		},
	},
	exact inductive_class_contains_nat hφ
end

axiom infinity_axiom : ∃I, is_inductive I

theorem nat_is_set : is_set nat :=
begin 
	cases infinity_axiom with I hI,
	apply @subclass_of_set_is_set nat I,
	exact inductive_set_contains_nat hI,
end


def ω : Set := classical.some nat_is_set

lemma tran_set_of_ord_is_ord {x : Set} (x_tran : transitive x) (x_ords : subset_class x ON) : 
ordinal x := 
{
	tran := x_tran,
	wo := 
	{
		irrfl := λy hy, ON_ordinal_class.wo.irrfl (x_ords hy),
		tran := λa b c ha hb hc hab hbc, ON_ordinal_class.wo.tran 
		(x_ords ha) (x_ords hb) (x_ords hc) hab hbc,
		tri := λa b ha hb, ON_ordinal_class.wo.tri (x_ords ha) (x_ords hb),
		wf := λX hX1 hX2, ON_ordinal_class.wo.wf (λy hy, x_ords (hX1 hy)) hX2,
	}
}

@[simp]lemma mem_omega : ∀x, x ∈ ω ↔ x ∈ nat := classical.some_spec nat_is_set

theorem induction_set {I : Set} (hI : is_inductive I) (h : I ⊆ ω) : I = ω :=
begin 
	rw eq_iff_subsets,
	use h,
	have := inductive_set_contains_nat hI,
	intros n hn,
	simp at hn,
	exact this hn,
end

theorem induction_class {I : fclass} (hI : inductive_class I) (h : subclass_set I ω) : 
∃I_set : is_set I, set_of I_set = ω :=
begin 
	have I_set := subclass_of_set_is_set h,
	use I_set,
	have h1 : is_inductive (set_of I_set),
	{
		split,
		{
			simp,
			exact hI.1,
		},
		{
			simp,
			exact hI.2,
		},
	},
	have h2 : set_of I_set ⊆ ω,
	{
		intros x hx,
		simp at hx,
		exact h hx,
	},
	exact induction_set h1 h2,
end

theorem omega_ord : ordinal ω :=
begin 
	apply tran_set_of_ord_is_ord,
	{
		intros n hn m hm,
		rw mem_omega at *,
		exact mem_of_nat_is_nat hn hm,
	},
	{
		intros n hn,
		rw mem_omega at hn,
		exact nonempty.intro (nat_is_ord hn),
	}
end

lemma ord_contains_empty {x : Set} (x_ord : ordinal x) (x_nonempty : x ≠ ∅) : ∅ ∈ x :=
begin 
	rcases x_ord.wo.wf (subset_self x) x_nonempty with ⟨t, htx, t_min⟩,
	have h_inter : t ∩ x = ∅,
	{
		by_contra h,
		cases nonempty_has_mem h with a ha,
		simp at ha,
		exact t_min ha.2 ha.1,
	},
	have t_ss := x_ord.tran htx,
	by_cases contra : t = ∅,
	{rw← contra, exact htx,},
	{
		exfalso,
		cases nonempty_has_mem contra with a ha,
		have : a ∈ t ∩ x,
		{
			rw mem_pair_inter,
			exact ⟨ha, t_ss ha⟩,
		},
		rw h_inter at this,
		exact (mem_empty a).mp this,
	},
end

lemma lim_ordinal_is_inductive {x : Set} {x_ord : ordinal x} (x_lim : is_limit x_ord) :
 is_inductive x :=
 begin 
	 split,
	 {exact ord_contains_empty x_ord x_lim.1},
	 intros y hy,
	 have y_ord : ordinal y := mem_ord_is_ord x_ord hy,
	 cases ON_ordinal_class.wo.tri (mem_ON_of_ord x_ord) 
	 (mem_ON_of_ord (succ_of_ordinal_is_ordinal y_ord)),
	 {
		 rw mem_succ at h,
		 cases h,
		 {
			 exfalso,
			 exact not_ord_mem_ord x_ord h hy,
		 },
		 {
			 rw h at hy,
			 exfalso,
			 exact ord_not_mem_self (mem_ON_of_ord y_ord) hy,
		 },
	 },
	 cases h,
	 {exact h},
	 {
		 exfalso,
		 apply x_lim.2,
		 use [y, y_ord],
		 exact h,
	 }
 end

theorem ω_smallest_lim : is_limit omega_ord ∧ ∀⦃α⦄ (α_ord : ordinal α), is_limit α_ord → ω ≤ α :=
begin 
	split,
	{
		split,
		{
			intro h,
			have := empty_is_nat,
			rw← mem_omega at this,
			rw h at this,
			exact (mem_empty ∅).mp this,
		},
		{
			intro h,
			rcases h with ⟨x, x_ord, hx⟩,
			have x_nat : x ∈ nat,
			{
				have := lt_succ_self x,
				rw← hx at this,
				unfold has_lt.lt at this,
				rw mem_omega at this,
				exact this,
			},
			have sx_nat := succ_of_nat_is_nat x_nat,
			rw← hx at sx_nat,
			rw← mem_omega at sx_nat,
			exact ord_not_mem_self (mem_ON_of_ord omega_ord) sx_nat,
		},
	},
	{
		intros α α_ord h,
		rw ← ord_le_iff_subset (mem_ON_of_ord omega_ord) (mem_ON_of_ord α_ord),
		have := lim_ordinal_is_inductive h,
		intros n hn,
		simp at hn,
		exact inductive_set_contains_nat this hn,
	}
end

lemma sing_is_pair (x : Set) : pair_set x x = sing x := rfl
lemma sing_eq (x y : Set) : sing x = sing y ↔ x = y := 
begin 
	split,
	{
		intro h,
		have : x ∈ sing x := (mem_sing x x).mpr rfl,
		rw h at this,
		simp at this,
		exact this,
	},
	{
		exact congr_arg (λ (x : Set), sing x),
	},
end

lemma mem_pair_fst (a b : Set) : a ∈ pair_set a b :=
begin 
	rw mem_pair,
	exact or.inl rfl,
end

lemma mem_pair_snd (a b : Set) : b ∈ pair_set a b :=
begin 
	rw mem_pair,
	exact or.inr rfl,
end

def ord_pair (x y : Set) := pair_set (sing x) (pair_set x y)

lemma ord_pair_eq {x y a b : Set} : ord_pair x y = ord_pair a b → x = a ∧ y = b := 
begin 
	unfold ord_pair,

	intro h,
	by_cases hxy : x = y,
	{
		rw← hxy at h,
		rw sing_is_pair at h,
		rw sing_is_pair at h,
		have hx : sing x ∈ pair_set (sing a) (pair_set a b),
		{rw← h, simp},
		simp at hx,
		cases hx,
		{
			rw sing_eq at hx,
			use hx,
			have : (pair_set a b) ∈ sing (sing x),
			{rw h, rw mem_pair, exact or.inr rfl},
			simp at this,
			rw hx at this,
			have hb := mem_pair_snd a b,
			rw this at hb,
			rw mem_sing at hb,
			exact (eq.congr hxy (eq.symm hb)).mp hx,
		},
		{
			have ha := mem_pair_fst a b,
			rw← hx at ha,
			rw mem_sing at ha,
			use ha.symm,

			have hb := mem_pair_snd a b,
			rw ← hx at hb,
			rw mem_sing at hb,
			exact (rfl.congr (eq.symm hb)).mp (eq.symm hxy),
		},
	},
	{
		have hxa : x = a,
		{
			have hx := mem_pair_fst (sing x) (pair_set x y),
			rw h at hx, simp at hx,
			cases hx,
			{exact (sing_eq x a).mp hx},
			{
				have := mem_pair_fst a b,
				rw← hx at this, simp at this,
				exact this.symm,
			},
		},
		use hxa,

		have temp := mem_pair_snd (sing x) (pair_set x y),
		rw h at temp, simp at temp,
		cases temp,
		{
			exfalso,
			have := mem_pair_snd x y,
			rw temp at this, simp at this,
			finish,
		},
		{
			have := mem_pair_snd x y,
			rw temp at this, simp at this,
			cases this,
			{exfalso,finish},
			{exact this},
		},
	}
end

lemma ord_pair_eq_iff (x y a b : Set) : 
ord_pair x y = ord_pair a b ↔ x = a ∧ y = b := 
begin 
	split,
	{exact ord_pair_eq},
	{
		intro h,
		exact congr (congr_arg ord_pair h.1) h.2,
	},
end

def is_ord_pair (x : Set) : Prop := ∃a b, x = ord_pair a b

def set_relation (x : Set) : Prop := ∀⦃y⦄, y ∈ x → is_ord_pair y
def set_function (x : Set) : Prop := ∀⦃y⦄, y ∈ x → ∃b a, y = ord_pair a b ∧ ∀⦃c⦄,
 ord_pair a c ∈ x → b = c

def function (φ : relation) := ∀x, ∃y, φ x y ∧ ∀z, φ x z → y = z
def function_on_set (φ : relation) (X : Set) 
:= ∀⦃x⦄, x ∈ X → ∃y , φ x y ∧ ∀z, φ x z → y = z

axiom replacement_axiom {φ : relation} (h : function φ) (A : Set) : 
∃B : Set, ∀⦃y⦄, (∃⦃z⦄ (hz : z ∈ A), φ z y) → y ∈ B

lemma replacement' {φ : relation} (h : function φ) (A : Set) : 
∃B : Set, ∀⦃y⦄, (∃⦃z⦄ (hz : z ∈ A), φ z y) ↔ y ∈ B :=
begin
	cases replacement_axiom h A with B hB,

	let P := λx, (∃⦃z⦄ (hz : z ∈ A), φ z x),
	have hP : subclass_set P B,
	{
		intros t ht,
		apply hB,
		rcases ht with ⟨z, hz1, hz2⟩,
		use z,
		exact ⟨hz1, hz2⟩,
	},

	cases (subclass_of_set_is_set hP) with C hC,
	use C,
	intro y,
	rw hC y,
end

lemma domain_exists (x : Set) : ∃D : Set, ∀z, z ∈ D ↔ (∃b, ord_pair z b ∈ x) :=
begin 
	let φ := λn m, (∃b, n = ord_pair m b) ∨ (¬is_ord_pair n ∧ m = ∅),
	have := @replacement_axiom φ _ x, swap,
	{
		intros n,
		by_cases is_ord_pair n,
		{
			rcases h with ⟨m, b, hmb⟩,
			use m,
			split,
			{
				left,
				use b,
				exact hmb,
			},
			{
				intros m' hm',
				cases hm',
				{
					cases hm' with b' hb',
					rw hb' at hmb,
					exact (ord_pair_eq hmb).1.symm,
				},
				{
					exfalso, 
					apply hm'.1,
					use [m, b],
					exact hmb,
				},
			},
		},
		{
			use ∅,
			split,
			{
				right,
				use h,
			},
			{
				intros z hz,
				cases hz,
				{
					exfalso,
					cases hz with b hb,
					apply h,
					use [z, b],
					exact hb,
				},
				{
					exact hz.2.symm,
				},
			},
		},
	},
	let P := λz, ∃ (b : Set), ord_pair z b ∈ x,
	cases this with B hB,
	have hP : subclass_set P B,
	{
		intros y hy,
		apply hB,
		cases hy with t ht,
		use ord_pair y t, use ht,
		finish,
	},
	cases (subclass_of_set_is_set hP) with D hD,
	use D,
	finish,
end

def domain (x : Set) : Set := classical.some (domain_exists x)
@[simp]lemma mem_domain (y x : Set) : y ∈ domain x ↔ ∃ (b : Set), ord_pair y b ∈ x
:= classical.some_spec (domain_exists x) y

lemma inv_exists (X : Set) : 
∃I : Set, ∀m, m ∈ I ↔ ∃n a b, (n ∈ X ∧ n = ord_pair a b ∧ m = ord_pair b a) :=
begin 
	let φ := λn m, (∃a b, n = ord_pair a b ∧
	m = ord_pair b a) ∨ (¬is_ord_pair n ∧ m = ∅),

	have := @replacement_axiom φ _ X, swap,
	{
		intros n,
		by_cases is_ord_pair n,
		{
			rcases h with ⟨a, b, hab⟩,
			use ord_pair b a,
			split,
			{
				left,
				use [a, b],
				exact ⟨hab, rfl⟩,
			},
			{
				intros m' hm',
				cases hm',
				{
					rcases hm' with ⟨a', b', hab'⟩,
					rw hab'.1 at hab,
					rw hab'.2,
					rw ord_pair_eq_iff at *,
					tauto,
				},
				{
					exfalso,
					apply hm'.1,
					use [a, b],
					exact hab,
				},
			},
		},
		{
			use ∅,
			split,
			{right, use h,},
			{
				intros m hm,
				cases hm,
				{
					exfalso,
					apply h,
					rcases hm with ⟨a, b, hab⟩,
					use [a, b],
					exact hab.1,
				},
				{exact hm.2.symm,},
			},
		},
	},
	 
	let P := λm, ∃ (n a b : Set), n ∈ X ∧ n = ord_pair a b ∧ m = ord_pair b a,
	cases this with B hB,
	have hP : subclass_set P B,
	{
		intros m hm,
		apply hB,
		rcases hm with ⟨x, a, b, hx⟩,
		use ord_pair a b,
		split,
		{finish},
		{
			left,
			finish,
		},
	},
	cases (subclass_of_set_is_set hP) with I hI,
	use I,
	exact hI,
end

def inv (x : Set) : Set := classical.some (inv_exists x)
@[simp]lemma mem_inv (y x : Set) : 
y ∈ inv x ↔ ∃ (n a b : Set), n ∈ x ∧ n = ord_pair a b ∧ y = ord_pair b a :=
classical.some_spec (inv_exists x) y

def range (x : Set) : Set := domain (inv x)
@[simp]lemma mem_range (y x : Set) : y ∈ range x ↔ ∃a, ord_pair a y ∈ x :=
begin 
	unfold range,
	simp,
	split,
	{
		intro h,
		rcases h with ⟨b, n, hn, c, d, hcd⟩,
		use c,
		suffices hn2 : n = ord_pair c y,
		{
			rw← hn2,
			exact hn,
		},
		{
			rw hcd.1,
			rw ord_pair_eq_iff at *,
			use rfl,
			finish,
		},
	},
	{
		intro h,
		cases h with a ha,
		use [a, ord_pair a y, ha, a, y, rfl],
	},
end

lemma eval_exists {f x : Set} (f_func : set_function f) (hx : x ∈ domain f) :
∃(y : Set) (hy : y ∈ range f), ord_pair x y ∈ f :=
begin 
	rw mem_domain at hx,
	cases hx with y hy,
	use y,
	simp,
	split,
	{
		use x,
		exact hy,
	},
	{exact hy},
end

def eval {f x : Set} (f_func : set_function f) (hx : x ∈ domain f) := 
classical.some (eval_exists f_func hx)

lemma eval_spec {f x : Set} (f_func : set_function f) (hx : x ∈ domain f)
: ∃(hy : eval f_func hx ∈ range f), ord_pair x (eval f_func hx ) ∈ f :=
classical.some_spec (eval_exists f_func hx)

infix ` @@ `: 1000 := eval

lemma eval_unique {f x : Set} (f_func : set_function f) (hx : x ∈ domain f) {y : Set} :
ord_pair x y ∈ f → y = f_func @@ hx := 
begin
	intro h,
	cases eval_spec f_func hx with hord hpair,
	rcases f_func hpair with ⟨b, a, hab⟩,
	rw ord_pair_eq_iff at hab,
	cases hab,
	rw← hab_left.1 at hab_right,
	rw← hab_left.2 at hab_right,
	exact (hab_right h).symm,
end

lemma mem_range_iff_eval {f : Set} (f_func : set_function f) : ∀⦃y⦄, y ∈ range f ↔
 ∃(x : Set) (hx : x ∈ domain f), y = f_func @@ hx :=
begin 
	intro y,
	split,
	{
		intro h,
		simp at h,
		cases h with a ha,
		use a,
		have haf : a ∈ domain f,
		{
			simp,
			use y,
			exact ha,
		},
		use haf,
		apply eval_unique f_func haf ha,
	},
	{
		intro h,
		simp,
		rcases h with ⟨a, haf, ha⟩,
		use a,
		rw mem_domain at haf,
		cases haf with b hb,
		rw ha,
		cases eval_spec f_func haf with heval,
		exact h,
	},
end

def injective {f : Set} (f_func : set_function f) := 
∀⦃x y⦄ {hxf : x ∈ domain f} {hyf : y ∈ domain f}, f_func @@ hxf = f_func @@ hyf →
x = y

structure full_func (f : Set) :=
(f_func : set_function f)
(codomain : Set)
(h_codomain : range f ⊆ codomain)

def surjective {f : Set} (f_func : full_func f) := f_func.codomain ⊆ range f

lemma surjective_iff_eq {f : Set} (f_func : full_func f) : 
surjective f_func ↔ f_func.codomain = range f :=
begin 
	split,
	{
		rw eq_iff_subsets,
		intro h,
		use h,
		exact f_func.h_codomain,
	},
	{
		intro h,
		unfold surjective,
		rw h,
		exact subset_self (range f),
	},
end

lemma inv_of_inj_is_func {f : Set} {f_func : set_function f}
(f_inj : injective f_func) : set_function (inv f) :=
begin 
	intros p hp,
	rw mem_inv at hp,
	rcases hp with ⟨n, a, b, hn⟩,
	use [a, b],
	split,
	{
		rw hn.2.2,
	},
	{
		intros c hc,
		rw mem_inv at hc,
		rcases hc with ⟨m, a', b', hm⟩,
		rw ord_pair_eq_iff at hm,
		rcases hm with ⟨hm1, hm2, hm3⟩,
		rw [←hm3.1, ←hm3.2] at hm2,
		rw hm2 at hm1,
		rcases hn with ⟨hn1, hn2, hn3⟩,
		rw hn2 at hn1,
		have haf : a ∈ domain f,
		{
			rw mem_domain,
			use [b, hn1],
		},
		have hcf : c ∈ domain f,
		{
			rw mem_domain,
			use [b, hm1],
		},
		have hba := eval_unique f_func haf hn1,
		have hbc := eval_unique f_func hcf hm1,
		rw hba at hbc,
		exact f_inj hbc,
	},
end

structure bijection (f : Set) extends full_func f :=
(injective : injective f_func)
(surjective : surjective (full_func.mk f_func codomain h_codomain))

def same_card (x y : Set) := 
∃(f : Set) (f_bi : bijection f), domain f = x ∧ f_bi.codomain = y

lemma restricted_replacement {φ : relation} {X : Set} (hφ : function_on_set φ X) :
∃B : Set, ∀z, z ∈ B ↔ ∃x ∈ X, φ x z := 
begin 
	let P := λ x y, (x ∈ X ∧ φ x y) ∨ (x ∉ X ∧ y = ∅),
	have P_func : function P,
	{
		intro x,
		by_cases hx : x ∈ X,
		{
			cases hφ hx with y hy,
			use y,
			split,
			{
				left,
				use [hx, hy.1],
			},
			{
				intros y' hy',
				cases hy',
				{exact hy.2 y' hy'.2},
				{finish},
			},
		},
		{
			use ∅,
			split,
			{
				right,
				use hx,
			},
			{
				intros z hz,
				cases hz,
				{finish},
				{finish},
			},
		},
	},

	cases replacement_axiom P_func X with C hC,
	have h_subclass : subclass_set (λ z, ∃ (x : Set) (H : x ∈ X), φ x z) C := 
	by finish,

	cases subclass_of_set_is_set h_subclass with B hB,
	use B,
	exact hB,
end


lemma prod_exists (A B : Set) : ∃C : Set, ∀p, p ∈ C ↔
 ∃a b, a ∈ A ∧ b ∈ B ∧ p = ord_pair a b :=
begin 
	have lem_1 : ∀⦃a⦄, a ∈ A → ∃ D : Set, ∀p, p ∈ D ↔ ∃b, b ∈ B ∧ p = ord_pair a b,
	{
		intros a ha,
		let φ := λx y, y = ord_pair a x,
		have φ_func : function_on_set φ B,
		{
			intros x hx,
			use ord_pair a x,
			split,
			{exact rfl,},
			{exact λ {b : Set}, eq_comm.mpr},
		},

		cases restricted_replacement φ_func with D hD,
		use D,
		finish,
	},
	let φ := λx y, ∀p, p ∈ y ↔ ∃b, b ∈ B ∧ p = ord_pair x b,
	have φ_func : function_on_set φ A,
	{
		intros a ha,
		cases lem_1 ha with y hy,
		use y,
		split,
		{exact hy},
		{
			intros z hz,
			ext,
			exact iff.trans (hy z_1) (iff.symm (hz z_1)),
		},
	},
	cases restricted_replacement φ_func with F hF,
	use union F,
	simp,
	intros p,
	split,
	{
		intro h,
		cases h with Y hY,
		rw hF at hY,
		cases hY with temp hpY,
		rcases temp with ⟨a, ha, hφa⟩,
		use [a, ha],
		rw hφa p at hpY,
		cases hpY with x hx,
		use [x, hx.1, hx.2],
	},
	{
		intro h,
		rcases h with ⟨a, haA, b, hbB, hbp⟩,
		cases lem_1 haA with Y hY,
		use Y,
		split,
		{
			rw hF,
			use [a, haA],
			exact hY,
		},
		{
			rw hY,
			use [b, hbB, hbp],
		},
	},
end

def prod (A B : Set) := classical.some (prod_exists A B)

class has_set_prod (α β : Type 1) (γ : out_param (Type 1)) :=
(prod : α → β → γ)

infix ` × ` :72 := prod

lemma mem_prod (A B : Set) : ∀p, p ∈ A × B ↔ ∃a b, a ∈ A ∧ b ∈ B ∧ p = ord_pair a b
:= classical.some_spec (prod_exists A B)

lemma mem_prod_pair (a b A B : Set) : ord_pair a b ∈ A × B ↔ a ∈ A ∧ b ∈ B :=
begin 
	rw mem_prod,
	split,
	{
		intro h,
		rcases h with ⟨x, y, hxy⟩,
		rw ord_pair_eq_iff at hxy,
		finish,
	},
	{
		intro h,
		use [a, b, h.1, h.2],
	},
end

instance : has_singleton Set Set := ⟨sing⟩

instance : has_insert Set Set :=
⟨λ a s, sing a ∪ s⟩

lemma helper : ∀x : Set, sing x ∪ ∅ = sing x := 
begin 
	intros x,
	ext,
	simp,
end

instance : is_lawful_singleton Set Set := ⟨helper⟩

def set_restriction (f A : Set) := 
classical.some (specification_axiom f (λx, ∃a b, a ∈ A ∧ x = ord_pair a b))

lemma mem_restriction (f A : Set) :
 ∀x, x ∈ set_restriction f A ↔ x ∈ f ∧ ∃a b, a ∈ A ∧ x = ord_pair a b :=
classical.some_spec (specification_axiom f (λx, ∃a b, a ∈ A ∧ x = ord_pair a b))

lemma is_func_restriction {f : Set} (A : Set) (f_func : set_function f) :
 set_function (set_restriction f A) := 
begin 
	intros x hx,
	rw mem_restriction at hx,
	rcases hx with ⟨hxf, a, b, hab⟩,
	use [b, a, hab.2],
	intros c hc,
	rw mem_restriction at hc,
	rw hab.2 at hxf,
	rcases f_func hxf with ⟨c', a', hac1, hac2⟩,
	rw ord_pair_eq_iff at hac1,
	rw hac1.1 at hc,
	rw hac1.2,
	exact hac2 hc.1,
 end

def comp (g f : Set) := 
classical.some (specification_axiom ((domain f) × range g) 
(λp, ∃x y z, ord_pair x z ∈ f ∧ ord_pair z y ∈ g))

lemma mem_comp (g f : Set) : 
∀p, p ∈ comp g f ↔ p ∈ (domain f × range g) ∧
∃x y z, ord_pair x z ∈ f ∧ ord_pair z y ∈ g := classical.some_spec
((specification_axiom ((domain f) × range g) 
(λp, ∃x y z, ord_pair x z ∈ f ∧ ord_pair z y ∈ g)))


end test