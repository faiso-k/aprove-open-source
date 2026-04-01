package aprove.verification.idpframework.Core.Utility.Marking;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;


/**
 *
 * @author MP
 */
public class QuantifiedConjunction<T> extends MarkContent.MarkContentSkeleton<QuantifiedConjunction<T>, T> {

    protected final ImmutableList<ItpfQuantor> quantification;

    public QuantifiedConjunction(final ImmutableList<ItpfQuantor> quantification, final T item) {
        super(ImmutableCreator.create(Collections.singleton(item)));
        this.quantification = quantification;
    }

    public QuantifiedConjunction() {
        super(ImmutableCreator.create(Collections.<T>emptySet()));
        this.quantification = ItpfFactory.EMPTY_QUANTORS;
    }

    public QuantifiedConjunction(final ImmutableList<ItpfQuantor> quantification, final ImmutableCollection<T> items) {
        super(items);
        this.quantification = quantification;
    }

    public ImmutableList<ItpfQuantor> getQuantification() {
        return this.quantification;
    }

    @Override
    public void export(final StringBuilder sb,
        final Export_Util eu,
        final VerbosityLevel verbosityLevel) {
        if (this.items.isEmpty()) {
            sb.append("TRUE");
        } else {
            for (final ItpfQuantor quantor : this.quantification) {
                quantor.export(sb, eu, verbosityLevel);
                sb.append(" ");
            }

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
