import tlc2.value.impl.BoolValue;
import tlc2.value.impl.FcnRcdValue;
import tlc2.value.impl.TupleValue;
import tlc2.value.impl.Value;
import util.Assert;

public class PageQueue {

	/**
	 * NoDuplicates(seq) == \A i,j \in 1..Len(seq): i # j => seq[i] # seq[j]
	 */
	public static BoolValue NoDuplicates(Value v1) {
		Value[] values = null;
		
		if (v1 instanceof FcnRcdValue) {
			final FcnRcdValue frv = (FcnRcdValue) v1;
			values = frv.values;
		} else if (v1 instanceof TupleValue) {
			final TupleValue tv = (TupleValue) v1;
			values = tv.elems;
		} else {
			Assert.fail(String.format("Incompatible parameter type (was: %s)", v1.getClass().getName()));
		}
		
		for (int i = 0; i < values.length; i++) {
			for (int j = i + 1; j < values.length; j++) {
				if (values[i].equals(values[j])) {
					return BoolValue.ValFalse;
				}
			}
		}
		
		return BoolValue.ValTrue;
	}
}
