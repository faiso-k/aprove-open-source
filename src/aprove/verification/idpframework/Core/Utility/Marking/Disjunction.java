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
public class Disjunction<T> extends MarkContent.MarkContentSkeleton<Disjunction<T>, T> {

    public Disjunction(final T item) {
        super(ImmutableCreator.create(Collections.singleton(item)));
    }

    public Disjunction() {
        super(ImmutableCreator.create(Collections.<T>emptySet()));
    }

    public Disjunction(final ImmutableCollection<T> items) {
        super(items);
    }

    @Override
    public void export(final StringBuilder sb,
        final Export_Util eu,
        final VerbosityLevel verbosityLevel) {
        if (this.items.isEmpty()) {
            sb.append("FALSE");
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
                    sb.append(eu.orSign());
                    sb.append(" ");
                }
            }
        }
    }

}
