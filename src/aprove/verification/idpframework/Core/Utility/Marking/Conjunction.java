package aprove.verification.idpframework.Core.Utility.Marking;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;


/**
 *
 * @author MP
 */
public class Conjunction<T> extends MarkContent.MarkContentSkeleton<Conjunction<T>, T> {

    public Conjunction(final T item) {
        super(ImmutableCreator.create(Collections.singleton(item)));
    }

    public Conjunction() {
        super(ImmutableCreator.create(Collections.<T>emptySet()));
    }

    public Conjunction(final ImmutableCollection<T> items) {
        super(items);
    }

    @Override
    public void export(final StringBuilder sb,
        final Export_Util eu,
        final VerbosityLevel verbosityLevel) {
        if (this.items.isEmpty()) {
            sb.append("TRUE");
        } else {
            final Iterator<T> contentIterator = this.items.iterator();

            while(contentIterator.hasNext()) {
                final Object content = contentIterator.next();
                if (content instanceof IDPExportable) {
                    final IDPExportable exportableContent = (IDPExportable) content;
                    exportableContent.export(sb, eu, verbosityLevel);
                } else {
                    sb.append(content.toString());
                }

                if (contentIterator.hasNext()) {
                    sb.append(" ");
                    sb.append(eu.andSign());
                    sb.append(" ");
                }
            }
        }
    }

}
